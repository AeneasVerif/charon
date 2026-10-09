//! Reading values out of const-eval memory.
use super::*;
use interpret::GlobalAlloc;
use rustc_abi::{FieldIdx, Size};
use rustc_const_eval::const_eval::CompileTimeInterpCx;
use rustc_const_eval::interpret::{
    FnVal, ImmTy, Immediate, InterpResult, MPlaceTy, OpTy, Projectable, interp_ok,
};
use rustc_hir::def::DefKind;

impl<'tcx> ConstReader<'tcx> {
    /// Classify the given allocation.
    pub(crate) fn alloc_target(&self, alloc_id: interpret::AllocId) -> AllocTarget<'tcx> {
        let tcx = self.tcx;
        match tcx.global_alloc(alloc_id) {
            GlobalAlloc::Function { instance } => AllocTarget::Fn(instance),
            GlobalAlloc::Static(def_id)
                if let DefKind::Static { nested: false, .. } = tcx.def_kind(def_id) =>
            {
                AllocTarget::Global(GlobalRef::Static(def_id))
            }
            GlobalAlloc::Static(_) | GlobalAlloc::Memory(_) => {
                AllocTarget::Global(GlobalRef::Alloc(alloc_id))
            }
            GlobalAlloc::VTable(ty, preds) => AllocTarget::VTable(ty, preds),
            GlobalAlloc::TypeId { ty } => AllocTarget::TypeId(ty),
        }
    }

    /// Whether we refer to `global` by name in pointers to it, rather than inlining its contents.
    pub fn is_named_global(&self, global: GlobalRef) -> bool {
        match global {
            GlobalRef::Static(_) => true,
            // TODO: nested statics are synthetic items that make the rest of the machinery ICE,
            // so we don't name them yet.
            GlobalRef::Alloc(alloc_id) => {
                self.config.anon_allocs_as_globals
                    && matches!(self.tcx.global_alloc(alloc_id), GlobalAlloc::Memory(_))
            }
        }
    }

    /// Read the raw bytes of an evaluated operand, keeping track of uninitialized bytes and pointer
    /// provenance.
    pub(crate) fn read_raw_bytes(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        op: &OpTy<'tcx>,
    ) -> InterpResult<'tcx, Vec<Byte<'tcx>>> {
        op.as_mplace_or_imm().either(
            |mplace| self.read_mplace_bytes(ecx, &mplace),
            |imm| interp_ok(self.read_imm_bytes(&imm)),
        )
    }

    /// The bytes of an immediate, which is made of at most two scalars.
    fn read_imm_bytes(&self, imm: &ImmTy<'tcx>) -> Vec<Byte<'tcx>> {
        let mut bytes = vec![Byte::Uninit; imm.layout.size.bytes_usize()];
        let mut write = |offset: Size, scalar: interpret::Scalar| {
            match scalar {
                interpret::Scalar::Int(int) => {
                    let mut scalar = vec![0; int.size().bytes_usize()];
                    let endian = self.tcx.data_layout.endian;
                    interpret::write_target_uint(endian, &mut scalar, int.to_bits(int.size()))
                        .unwrap();
                    for (i, b) in scalar.into_iter().enumerate() {
                        bytes[offset.bytes_usize() + i] = Byte::Value(b);
                    }
                }
                interpret::Scalar::Ptr(ptr, size) => {
                    let target = self.alloc_target(ptr.provenance.alloc_id());
                    for i in 0..size.get() {
                        bytes[offset.bytes_usize() + i as usize] = Byte::Ptr(target, i);
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
    fn read_mplace_bytes(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        mplace: &MPlaceTy<'tcx>,
    ) -> InterpResult<'tcx, Vec<Byte<'tcx>>> {
        let size = mplace.layout.size;
        if size.bytes() == 0 {
            return interp_ok(vec![]);
        }
        let (alloc_id, offset, _) = ecx.ptr_get_alloc_id(mplace.ptr(), size.bytes() as i64)?;
        let alloc = ecx.get_alloc_raw(alloc_id)?;
        let range = interpret::alloc_range(offset, size);
        let raw_bytes = alloc.get_bytes_unchecked(range);
        let mut bytes: Vec<Byte<'tcx>> = (0..size.bytes())
            .map(
                |i| match alloc.init_mask().get(offset + Size::from_bytes(i)) {
                    true => Byte::Value(raw_bytes[i as usize]),
                    false => Byte::Uninit,
                },
            )
            .collect();

        // A pointer may straddle the boundaries of `range`.
        for (prov_range, prov) in alloc.provenance().get_range(range, ecx) {
            let target = self.alloc_target(prov.alloc_id());
            for i in 0..prov_range.size.bytes() {
                let pos = prov_range.start + Size::from_bytes(i);
                if range.start <= pos && pos < range.end() {
                    bytes[(pos - range.start).bytes_usize()] = Byte::Ptr(target, i as u8);
                }
            }
        }
        interp_ok(bytes)
    }

    /// The sized type that `tail`, the unsized tail of `place`, was unsized from. This is found in
    /// the metadata of the place.
    fn sized_tail(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        place: &MPlaceTy<'tcx>,
        tail: Ty<'tcx>,
    ) -> InterpResult<'tcx, Ty<'tcx>> {
        let tcx = self.tcx;
        let meta = place.meta().unwrap_meta();
        interp_ok(match tail.kind() {
            ty::Slice(_) | ty::Str => {
                let len = meta.to_target_usize(ecx)?;
                Ty::new_array(tcx, tail.sequence_element_type(tcx), len)
            }
            ty::Dynamic(preds, ..) => ecx.get_ptr_vtable_ty(meta.to_pointer(ecx), Some(preds))?,
            _ => unreachable!("unexpected unsized tail type {tail:?}"),
        })
    }

    /// Read a reference or raw pointer. Pointers to globals that we name are kept as pointers to
    /// these globals, and we fall back to reading the pointee for other cases.
    fn read_pointer(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        op: &OpTy<'tcx>,
    ) -> InterpResult<'tcx, Const<'tcx>> {
        let tcx = self.tcx;
        // Make sure we only read through if it's not dangling!
        let pointee = ecx.deref_pointer(op).discard_err().and_then(|place| {
            let (alloc_id, offset, _) = ecx.ptr_get_alloc_id(place.ptr(), 0).discard_err()?;
            Some((place, alloc_id, offset))
        });
        let Some((place, alloc_id, offset)) = pointee else {
            // Invalid pointer; try reading it as a raw address
            let int = ecx.read_scalar(op)?.try_to_scalar_int().unwrap();
            let kind = ConstKind::PtrNoProvenance(int.to_uint(int.size()));
            return interp_ok(Const {
                ty: op.layout.ty,
                kind,
            });
        };

        let ty = place.layout.ty;
        let (view_ty, unsize) = if place.layout.is_sized() {
            (Some(ty), None)
        } else {
            let tail = tcx.struct_tail_for_codegen(ty, self.typing_env);
            let sized_tail = self.sized_tail(ecx, &place, tail)?;
            // A slice or `dyn Trait` value is viewed at the sized type it was unsized from. Other
            // unsized values (e.g. a `CStr`) have no such type: we read them at their unsized type.
            let view_ty = matches!(ty.kind(), ty::Slice(_) | ty::Dynamic(..)).then_some(sized_tail);
            let unsize = Unsize {
                from: sized_tail,
                to: tail,
            };
            (view_ty, Some(unsize))
        };

        let target = match view_ty {
            Some(view_ty) => {
                let layout = tcx.layout_of(self.typing_env.as_query_input(view_ty));
                if offset == Size::ZERO
                    && let AllocTarget::Global(global) = self.alloc_target(alloc_id)
                    && self.is_named_global(global)
                    // TODO: A view over an anonymous allocation must cover exactly the whole
                    // allocation. Our constant pointers don't have a way to indicate their offset,
                    // so if there's a mismatch it would be wrong.
                    && (matches!(global, GlobalRef::Static(_))
                        || layout.is_ok_and(|layout| layout.size == ecx.get_alloc_info(alloc_id).size))
                {
                    PtrTarget::Global {
                        global,
                        ty: view_ty,
                    }
                } else {
                    // HACK: fallback to reading the value of the pointee, at type `view_ty`.
                    let place = if view_ty == ty {
                        place
                    } else {
                        place.offset(Size::ZERO, layout.unwrap(), ecx)?
                    };
                    PtrTarget::Inline(Box::new(self.read_op(ecx, place.into())?))
                }
            }
            None => PtrTarget::Inline(Box::new(self.read_op(ecx, place.into())?)),
        };
        let kind = ConstKind::Ptr { target, unsize };
        interp_ok(Const {
            ty: op.layout.ty,
            kind,
        })
    }

    /// Read an evaluated operand back as a structured constant.
    pub(crate) fn read_op(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        op: OpTy<'tcx>,
    ) -> InterpResult<'tcx, Const<'tcx>> {
        // Code inspired from `try_destructure_mir_constant_for_user_output` and
        // `const_eval::eval_queries::op_to_const`.
        let ty = op.layout.ty;
        // Helper for struct-likes.
        let read_fields = |of: OpTy<'tcx>, field_count| {
            (0..field_count)
                .map(move |i| {
                    let field_op = ecx.project_field(&of, FieldIdx::from_usize(i))?;
                    self.read_op(ecx, field_op)
                })
                .collect::<InterpResult<Vec<_>>>()
        };
        let kind = match ty.kind() {
            ty::Char | ty::Bool | ty::Uint(_) | ty::Int(_) | ty::Float(_) => {
                ConstKind::Scalar(ecx.read_scalar(&op)?.try_to_scalar_int().unwrap())
            }
            ty::Adt(adt_def, ..) if adt_def.is_union() => {
                ConstKind::Memory(self.read_raw_bytes(ecx, &op)?)
            }
            ty::Adt(adt_def, ..) => {
                let variant = ecx.read_discriminant(&op)?;
                let op = if adt_def.is_enum() {
                    ecx.project_downcast(&op, variant)?
                } else {
                    op
                };
                let field_count = adt_def.variants()[variant].fields.len();
                ConstKind::Aggregate {
                    variant: Some(variant),
                    fields: read_fields(op, field_count)?,
                }
            }
            // A closure is essentially an adt with funky generics and some builtin impls.
            ty::Closure(_, args) => ConstKind::Aggregate {
                variant: None,
                fields: read_fields(op, args.as_closure().upvar_tys().len())?,
            },
            ty::Tuple(args) => ConstKind::Aggregate {
                variant: None,
                fields: read_fields(op, args.len())?,
            },
            ty::Array(..) | ty::Slice(..) => {
                let mut elems = ecx.project_array_fields(&op)?;
                let mut fields = vec![];
                while let Some((_, elem)) = elems.next(ecx)? {
                    fields.push(self.read_op(ecx, elem)?);
                }
                ConstKind::Aggregate {
                    variant: None,
                    fields,
                }
            }
            ty::Str => ConstKind::Str(ecx.read_str(&op.assert_mem_place())?.to_owned()),
            ty::FnDef(..) => ConstKind::fn_def(ty),
            ty::FnPtr(..) => {
                let fn_ptr = ecx.read_pointer(&op)?;
                let FnVal::Instance(instance) = ecx.get_ptr_fn(fn_ptr)?;
                ConstKind::FnPtr(instance)
            }
            ty::RawPtr(..) | ty::Ref(..) => return self.read_pointer(ecx, &op),
            ty::Pat(..) => {
                let op = ecx.project_field(&op, FieldIdx::from_u16(0))?;
                self.read_op(ecx, op)?.kind
            }
            ty::Dynamic(..) => {
                let place = op.assert_mem_place();
                let concrete_ty = self.sized_tail(ecx, &place, ty)?;
                let layout = (self.tcx)
                    .layout_of(self.typing_env.as_query_input(concrete_ty))
                    .unwrap();
                let place = place.offset(Size::ZERO, layout, ecx)?;
                return self.read_op(ecx, place.into());
            }
            ty::Foreign(..)
            | ty::UnsafeBinder(..)
            | ty::CoroutineClosure(..)
            | ty::Coroutine(..)
            | ty::CoroutineWitness(..) => ConstKind::Unsupported("Unhandled constant type"),
            ty::Alias(..)
            | ty::Param(..)
            | ty::Bound(..)
            | ty::Placeholder(..)
            | ty::Infer(..)
            | ty::Never
            | ty::Error(..) => {
                unreachable!("evaluated constant of invalid type {ty:?}")
            }
        };
        interp_ok(Const { ty, kind })
    }
}
