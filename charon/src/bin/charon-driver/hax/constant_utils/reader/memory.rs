//! Reading values out of const-eval memory.
use super::*;

/// Read the raw bytes of an evaluated operand, keeping track of uninitialized bytes and pointer
/// provenance. Used for values that have no structured representation (e.g. unions).
pub(crate) fn op_to_raw_bytes<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    ecx: &const_eval::CompileTimeInterpCx<'tcx>,
    op: &rustc_const_eval::interpret::OpTy<'tcx>,
) -> InterpResult<'tcx, Vec<ConstantByte>> {
    op.as_mplace_or_imm().either(
        |mplace| mplace_to_raw_bytes(s, ecx, &mplace),
        |imm| interp_ok(imm_to_raw_bytes(s, &imm)),
    )
}

/// The bytes of an immediate, which is made of at most two scalars.
fn imm_to_raw_bytes<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    imm: &rustc_const_eval::interpret::ImmTy<'tcx>,
) -> Vec<ConstantByte> {
    use rustc_abi::Size;
    use rustc_const_eval::interpret::Immediate;
    let mut bytes = vec![ConstantByte::Uninit; imm.layout.size.bytes_usize()];
    let mut write = |offset: Size, scalar: interpret::Scalar| {
        match scalar {
            interpret::Scalar::Int(int) => {
                let mut scalar = vec![0; int.size().bytes_usize()];
                let endian = s.base().tcx.data_layout.endian;
                interpret::write_target_uint(endian, &mut scalar, int.to_bits(int.size())).unwrap();
                for (i, b) in scalar.into_iter().enumerate() {
                    bytes[offset.bytes_usize() + i] = ConstantByte::Value(b);
                }
            }
            interpret::Scalar::Ptr(ptr, size) => {
                let prov = alloc_target(s, ptr.provenance.alloc_id()).sinto(s);
                for i in 0..size.get() {
                    bytes[offset.bytes_usize() + i as usize] =
                        ConstantByte::Provenance(prov.clone(), i);
                }
            }
        };
    };
    match **imm {
        Immediate::Uninit => {}
        Immediate::Scalar(a) => write(Size::ZERO, a),
        Immediate::ScalarPair(a, b) => {
            let rustc_abi::BackendRepr::ScalarPair { b_offset, .. } = imm.layout.backend_repr
            else {
                unreachable!()
            };
            write(Size::ZERO, a);
            write(b_offset, b);
        }
    }
    bytes
}

/// The bytes of a value in memory.
fn mplace_to_raw_bytes<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    ecx: &const_eval::CompileTimeInterpCx<'tcx>,
    mplace: &rustc_const_eval::interpret::MPlaceTy<'tcx>,
) -> InterpResult<'tcx, Vec<ConstantByte>> {
    use rustc_abi::Size;
    let size = mplace.layout.size;
    if size.bytes() == 0 {
        return interp_ok(vec![]);
    }
    let (alloc_id, offset, _) = ecx.ptr_get_alloc_id(mplace.ptr(), size.bytes() as i64)?;
    let alloc = ecx.get_alloc_raw(alloc_id)?;
    let range = interpret::alloc_range(offset, size);
    let raw_bytes = alloc.get_bytes_unchecked(range);
    let mut bytes: Vec<ConstantByte> = (0..size.bytes())
        .map(
            |i| match alloc.init_mask().get(offset + Size::from_bytes(i)) {
                true => ConstantByte::Value(raw_bytes[i as usize]),
                false => ConstantByte::Uninit,
            },
        )
        .collect();

    for (prov_range, prov) in alloc.provenance().get_range(range, ecx) {
        let prov = alloc_target(s, prov.alloc_id()).sinto(s);
        for i in 0..prov_range.size.bytes() {
            let pos = prov_range.start + Size::from_bytes(i);
            if range.start <= pos && pos < range.end() {
                bytes[(pos - range.start).bytes_usize()] =
                    ConstantByte::Provenance(prov.clone(), i as u8);
            }
        }
    }
    interp_ok(bytes)
}

/// The sized type that `tail`, the unsized tail of `place`, was unsized from. This is found in the
/// metadata of the place.
fn sized_tail<'tcx>(
    ecx: &const_eval::CompileTimeInterpCx<'tcx>,
    place: &rustc_const_eval::interpret::MPlaceTy<'tcx>,
    tail: ty::Ty<'tcx>,
) -> InterpResult<'tcx, ty::Ty<'tcx>> {
    use rustc_const_eval::interpret::Projectable;
    let tcx = *ecx.tcx;
    let meta = place.meta().unwrap_meta();
    interp_ok(match tail.kind() {
        ty::Slice(_) | ty::Str => {
            let len = meta.to_target_usize(ecx)?;
            ty::Ty::new_array(tcx, tail.sequence_element_type(tcx), len)
        }
        ty::Dynamic(preds, ..) => ecx.get_ptr_vtable_ty(meta.to_pointer(ecx), Some(preds))?,
        _ => unreachable!("unexpected unsized tail type {tail:?}"),
    })
}

/// Convert the target of a valid pointer. Pointers to globals are kept as references to these
/// globals, and we fallback to reading the bytes for other cases.
fn pointee_to_const<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    span: rustc_span::Span,
    ecx: &const_eval::CompileTimeInterpCx<'tcx>,
    place: rustc_const_eval::interpret::MPlaceTy<'tcx>,
) -> InterpResult<'tcx, (ConstantExpr, Option<UnsizingMetadata>)> {
    use rustc_const_eval::interpret::Projectable;
    let tcx = s.base().tcx;
    let ty = place.layout.ty;

    let (global_ty, metadata) = if place.layout.is_sized() {
        (Some(ty), None)
    } else {
        let tail = tcx.struct_tail_for_codegen(ty, s.typing_env());
        let sized_tail = sized_tail(ecx, &place, tail)?;
        // A slice or `dyn Trait` value is viewed at the sized type it was unsized from. Other
        // unsized values (e.g. a `CStr`) have no such type: we read them at their unsized type.
        let global_ty = matches!(ty.kind(), ty::Slice(_) | ty::Dynamic(..)).then_some(sized_tail);
        let ref_to = |ty| ty::Ty::new_imm_ref(tcx, tcx.lifetimes.re_static, ty);
        let metadata = compute_unsizing_metadata(s, ref_to(sized_tail), ref_to(tail));
        (global_ty, Some(metadata))
    };

    let (alloc_id, offset, _) = ecx.ptr_get_alloc_id(place.ptr(), 0)?;
    // TODO: A view over an anonymous allocation must cover exactly the whole allocation.
    // Our constant pointers don't have a way to indicate their offset, so if there's a
    // mismatch it would be wrong.
    let covers_alloc = |global_ty, global| match global {
        GlobalRef::Alloc(_) => {
            let alloc = tcx.global_alloc(alloc_id).unwrap_memory();
            tcx.layout_of(s.typing_env().as_query_input(global_ty))
                .is_ok_and(|layout| layout.size == alloc.inner().size())
        }
        GlobalRef::Static(_) => true,
    };
    if let Some(global_ty) = global_ty
        && offset == rustc_abi::Size::ZERO
        && let AllocTarget::Global(global) = alloc_target(s, alloc_id)
        && is_named_global(s, global)
        && covers_alloc(global_ty, global)
    {
        let kind = ConstantExprKind::NamedGlobal(global.sinto(s));
        interp_ok((kind.decorate(global_ty.sinto(s), span.sinto(s)), metadata))
    } else {
        // HACK: fallback to reading the bytes of the pointee, at the type of `global_ty`.
        let place = match global_ty {
            Some(global_ty) if global_ty != ty => {
                let layout = tcx
                    .layout_of(s.typing_env().as_query_input(global_ty))
                    .unwrap();
                // retype the place
                place.offset(rustc_abi::Size::ZERO, layout, ecx)?
            }
            _ => place,
        };
        interp_ok((op_to_const(s, span, ecx, place.into())?, metadata))
    }
}

/// Use the const-eval interpreter to convert an evaluated operand back to a structured
/// constant expression.
pub(crate) fn op_to_const<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    span: rustc_span::Span,
    ecx: &const_eval::CompileTimeInterpCx<'tcx>,
    op: rustc_const_eval::interpret::OpTy<'tcx>,
) -> InterpResult<'tcx, ConstantExpr> {
    use rustc_const_eval::interpret::Projectable;
    // Code inspired from `try_destructure_mir_constant_for_user_output` and
    // `const_eval::eval_queries::op_to_const`.
    let ty = op.layout.ty;
    // Helper for struct-likes.
    let read_fields = |of: rustc_const_eval::interpret::OpTy<'tcx>, field_count| {
        (0..field_count).map(move |i| {
            let field_op = ecx.project_field(&of, rustc_abi::FieldIdx::from_usize(i))?;
            op_to_const(s, span, ecx, field_op)
        })
    };
    let kind = match ty.kind() {
        ty::Char | ty::Bool | ty::Uint(_) | ty::Int(_) | ty::Float(_) => {
            let scalar = ecx.read_scalar(&op)?;
            let scalar_int = scalar.try_to_scalar_int().unwrap();
            let lit = scalar_int_to_constant_literal(s, scalar_int, ty);
            ConstantExprKind::Literal(lit)
        }
        ty::Adt(adt_def, ..) if adt_def.is_union() => {
            ConstantExprKind::Memory(op_to_raw_bytes(s, ecx, &op)?)
        }
        ty::Adt(adt_def, ..) => {
            let variant = ecx.read_discriminant(&op)?;
            let op = if adt_def.is_enum() {
                ecx.project_downcast(&op, variant)?
            } else {
                op
            };
            let field_count = adt_def.variants()[variant].fields.len();
            let fields = read_fields(op, field_count)
                .zip(&adt_def.variant(variant).fields)
                .map(|(value, field)| {
                    interp_ok(ConstantFieldExpr {
                        field: field.did.sinto(s),
                        value: value?,
                    })
                })
                .collect::<InterpResult<Vec<_>>>()?;
            ConstantExprKind::Adt {
                kind: get_variant_kind(adt_def, variant, s),
                fields,
            }
        }
        ty::Closure(def_id, args) => {
            // A closure is essentially an adt with funky generics and some builtin impls.
            let def_id: DefId = def_id.sinto(s);
            let field_count = args.as_closure().upvar_tys().len();
            let fields = read_fields(op, field_count)
                .map(|value| {
                    interp_ok(ConstantFieldExpr {
                        // HACK: Closure fields don't have their own def_id, but Charon doesn't use
                        // field DefIds so we put a dummy one.
                        field: def_id.clone(),
                        value: value?,
                    })
                })
                .collect::<InterpResult<Vec<_>>>()?;
            ConstantExprKind::Adt {
                kind: VariantKind::Struct,
                fields,
            }
        }
        ty::Tuple(args) => {
            let fields = read_fields(op, args.len()).collect::<InterpResult<Vec<_>>>()?;
            ConstantExprKind::Tuple { fields }
        }
        ty::Array(..) | ty::Slice(..) => {
            let len = op.len(ecx)?;
            let fields = (0..len)
                .map(|i| {
                    let op = ecx.project_index(&op, i)?;
                    op_to_const(s, span, ecx, op)
                })
                .collect::<InterpResult<Vec<_>>>()?;
            ConstantExprKind::Array { fields }
        }
        ty::Str => {
            let str = ecx.read_str(&op.assert_mem_place())?;
            ConstantExprKind::Literal(ConstantLiteral::Str(str.to_owned()))
        }
        ty::FnDef(def_id, args) => {
            let args = args.no_bound_vars().expect("bound variables in FnDef");
            let item = translate_item_ref(s, *def_id, args);
            ConstantExprKind::FnDef(item)
        }
        ty::FnPtr(..) => {
            let fn_ptr = ecx.read_pointer(&op)?;
            let FnVal::Instance(instance) = ecx.get_ptr_fn(fn_ptr)?;
            let def_id = instance.def_id();
            let generics = instance.args;
            let fun = translate_item_ref(s, def_id, generics);
            ConstantExprKind::FnPtr(fun)
        }
        ty::RawPtr(..) | ty::Ref(..) => {
            // Make sure we only read through if it's not dangling!
            let place_dangling = ecx.deref_pointer(&op).discard_err();
            let place = place_dangling
                .filter(|place| ecx.ptr_get_alloc_id(place.ptr(), 0).discard_err().is_some());
            if let Some(place) = place {
                // Valid pointer case
                let (val, metadata) = pointee_to_const(s, span, ecx, place)?;
                match ty.kind() {
                    ty::Ref(..) => ConstantExprKind::Borrow(val, metadata),
                    ty::RawPtr(.., mutability) => ConstantExprKind::RawBorrow {
                        arg: val,
                        mutability: mutability.sinto(s),
                        metadata,
                    },
                    _ => unreachable!(),
                }
            } else {
                // Invalid pointer; try reading it as a raw address
                let scalar = ecx.read_scalar(&op)?;
                let scalar_int = scalar.try_to_scalar_int().unwrap();
                let v = scalar_int.to_uint(scalar_int.size());
                let lit = ConstantLiteral::PtrNoProvenance(v);
                ConstantExprKind::Literal(lit)
            }
        }
        ty::Pat(..) => {
            let op = ecx.project_field(&op, FieldIdx::from_u16(0))?;
            *op_to_const(s, span, ecx, op)?.contents
        }
        ty::Dynamic(..) => {
            let place = op.assert_mem_place();
            let concrete_ty = sized_tail(ecx, &place, ty)?;
            let layout = (s.base().tcx)
                .layout_of(s.typing_env().as_query_input(concrete_ty))
                .unwrap();
            let place = place.offset(rustc_abi::Size::ZERO, layout, ecx)?;
            return op_to_const(s, span, ecx, place.into());
        }
        ty::Foreign(..)
        | ty::UnsafeBinder(..)
        | ty::CoroutineClosure(..)
        | ty::Coroutine(..)
        | ty::CoroutineWitness(..) => ConstantExprKind::Todo("Unhandled constant type".into()),
        ty::Alias(..) | ty::Param(..) | ty::Bound(..) | ty::Placeholder(..) | ty::Infer(..) => {
            fatal!(s[span], "Encountered evaluated constant of non-monomorphic type"; {op})
        }
        ty::Never | ty::Error(..) => {
            fatal!(s[span], "Encountered evaluated constant of invalid type"; {ty})
        }
    };
    let val = kind.decorate(ty.sinto(s), span.sinto(s));
    interp_ok(val)
}
