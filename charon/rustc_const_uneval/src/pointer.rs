//! Reading pointers out of const-eval memory.
use crate::*;
use rustc_abi::{FieldIdx, FieldsShape, Size};
use rustc_const_eval::const_eval::CompileTimeInterpCx;
use rustc_const_eval::interpret::{InterpResult, MPlaceTy, OpTy, Projectable, interp_ok};

impl<'tcx> ConstReader<'tcx> {
    /// Whether this allocation target should be read through a pointer -- it is otherwise
    /// read directly, breaking sharing.
    fn should_use_pointer(&self, tgt: AllocTarget) -> bool {
        match tgt {
            AllocTarget::Global(GlobalRef::Static(_)) => true,
            AllocTarget::Global(_) => self.config.anon_allocs_as_globals,
            AllocTarget::Fn(_) | AllocTarget::VTable(..) | AllocTarget::TypeId(..) => true,
        }
    }

    /// Read a reference or raw pointer. Pointers to globals that we name are kept as pointers to
    /// these globals, and we fall back to reading the pointee for other cases.
    pub(crate) fn read_pointer(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        op: &OpTy<'tcx>,
    ) -> InterpResult<'tcx, Const<'tcx>> {
        let tcx = self.tcx;
        let ptr_ty = op.layout.ty;
        let (ty::Ref(.., mutability) | ty::RawPtr(_, mutability)) = *ptr_ty.kind() else {
            unreachable!("not a pointer type: {ptr_ty:?}")
        };
        let place = ecx.deref_pointer(op)?;
        let ty = place.layout.ty;
        let unsize = if place.meta().has_meta() {
            let tail = tcx.struct_tail_for_codegen(ty, self.typing_env);
            let from = self.sized_tail(ecx, &place, tail)?;
            Some(Unsize { from, to: tail })
        } else {
            None
        };
        // The sized type at which we view the pointee, if any.
        let view_ty = match unsize {
            None => place.layout.is_sized().then_some(ty),
            Some(unsize) => self.is_viewed_unsized_from(ty).then_some(unsize.from),
        };

        // A pointer without provenance -- handle it separately to avoid ICEs.
        if let (None, addr) = place.ptr().into_raw_parts() {
            let addr = ConstKind::PtrNoProvenance(addr.bytes().into());
            let kind = match (unsize, view_ty) {
                (None, _) => match ptr_ty.kind() {
                    ty::TyKind::RawPtr(..) => addr,
                    ty::TyKind::Ref(..) => ConstKind::PtrCast {
                        ptr: Box::new(Const {
                            ty: Ty::new_ptr(tcx, ty, mutability),
                            kind: addr,
                        }),
                        unsize: None,
                    },
                    _ => unreachable!(),
                },
                // Unsize the thin pointer with the metadata.
                (Some(unsize), Some(view_ty)) => ConstKind::PtrCast {
                    ptr: Box::new(Const {
                        ty: Ty::new_ptr(tcx, view_ty, mutability),
                        kind: addr,
                    }),
                    unsize: Some(unsize),
                },
                // We don't have a sized type to unsize from, so we encode the pointer as bytes.
                (Some(_), None) => ConstKind::Memory(self.read_raw_bytes(ecx, op)?),
            };
            return interp_ok(Const { ty: ptr_ty, kind });
        }

        let (alloc_id, offset, _) = ecx.ptr_get_alloc_id(place.ptr(), 0)?;
        // A pointer into the allocation of a `TypeId` can only be expressed as bytes.
        if let AllocTarget::TypeId(_) = self.alloc_target(alloc_id) {
            let kind = ConstKind::Memory(self.read_raw_bytes(ecx, op)?);
            return interp_ok(Const { ty: ptr_ty, kind });
        }

        let alloc_target = self.alloc_target(alloc_id);
        let alloc_size = ecx.get_alloc_info(alloc_id).size;
        // A pointer outside of its allocation (one-past-the-end is fine) needs a wrapping offset.
        let in_bounds = offset <= alloc_size;

        // See if we can try reading this untyped allocation with a type, rather than bytes.
        if let AllocTarget::Global(GlobalRef::Alloc(alloc_id)) = alloc_target {
            self.alloc_types.update_if_unset(alloc_id, || {
                if offset != Size::ZERO {
                    return AllocView::Untyped;
                };

                // the sized type we will try reading with
                let pointee_ty = match unsize {
                    None if place.layout.is_sized() => ty,
                    Some(unsize) if ty == unsize.to => unsize.from,
                    _ => return AllocView::Untyped,
                };
                if let Ok(layout) = ecx.layout_of(pointee_ty)
                    && layout.size == alloc_size
                    && self.ty_covers_alloca(alloc_id, pointee_ty)
                {
                    AllocView::Typed(pointee_ty)
                } else {
                    AllocView::Untyped
                }
            })
        }

        let kind = if !in_bounds || self.should_use_pointer(alloc_target) {
            let (decl_ty, projections, end_ty) =
                self.place_in_global(ecx, &place, alloc_target, offset, in_bounds, view_ty)?;
            let target = PtrTarget::Global {
                target: alloc_target,
                ty: decl_ty,
                projections,
            };
            let (ty::Ref(.., mutability) | ty::RawPtr(_, mutability)) = *op.layout.ty.kind() else {
                unreachable!()
            };
            // We can't take a `*mut` to an immutable global, so we take a `*const` and cast it.
            let borrow_mutability = match alloc_target {
                AllocTarget::Global(global) => global.mutability(tcx).min(mutability),
                _ => mutability,
            };
            if Some(end_ty) == tcx.erase_and_anonymize_regions(view_ty)
                && borrow_mutability == mutability
                && !(op.layout.ty.is_ref() && mutability.is_mut())
            {
                ConstKind::Ptr { target, unsize }
            } else {
                // Point to the place we reached, then cast the pointer to the right type.
                let ptr = |ty, kind| Box::new(Const { ty, kind });
                let inner = ptr(
                    Ty::new_ptr(tcx, end_ty, borrow_mutability),
                    ConstKind::Ptr {
                        target,
                        unsize: None,
                    },
                );
                match (unsize, view_ty) {
                    // Cast to the sized type first, then unsize.
                    (Some(unsize), Some(view_ty)) => ConstKind::PtrCast {
                        ptr: ptr(
                            Ty::new_ptr(tcx, view_ty, mutability),
                            ConstKind::PtrCast {
                                ptr: inner,
                                unsize: None,
                            },
                        ),
                        unsize: Some(unsize),
                    },
                    (_, _) => ConstKind::PtrCast { ptr: inner, unsize },
                }
            }
        } else {
            // HACK: fallback to reading the value of the pointee, at type `view_ty`.
            let place = match view_ty {
                Some(view_ty) if view_ty != ty => {
                    place.offset(Size::ZERO, ecx.layout_of(view_ty)?, ecx)?
                }
                _ => place,
            };
            let target = PtrTarget::Inline(Box::new(self.read_op(ecx, place.into())?));
            ConstKind::Ptr { target, unsize }
        };
        interp_ok(Const { ty: ptr_ty, kind })
    }

    /// Whether reading `alloc_id` with type `ty` is possible without losing information.
    /// We do a simple under-approximate calculation to decide this:
    /// - all bytes are initialised
    /// - there are no provenance bytes
    /// - the read is valid at that type
    ///
    /// In practice we restrain this to integers, floats, chars, bools, and arrays of these.
    fn ty_covers_alloca(&self, alloc_id: interpret::AllocId, ty: Ty<'tcx>) -> bool {
        use ty::*;
        let mut elem_ty = ty;
        while let Array(ty, _) = elem_ty.kind() {
            elem_ty = *ty;
        }
        // we only handle these, because they must be initialised and can't store provenance.
        if !matches!(elem_ty.kind(), Int(_) | Uint(_) | Float(_) | Bool | Char) {
            return false;
        }
        // we look at the memory directly, as const-eval refuses to read mutable allocations.
        let Some(alloc) = GlobalRef::Alloc(alloc_id).memory(self.tcx) else {
            return false;
        };
        let alloc = alloc.inner();
        let range = interpret::alloc_range(Size::ZERO, alloc.size());
        let is_valid_elem = |bytes: &[u8]| {
            let value = interpret::read_target_uint(self.tcx.data_layout.endian, bytes).unwrap();
            match elem_ty.kind() {
                Bool => value <= 1,
                Char => char::try_from(value as u32).is_ok(),
                _ => true, // ints/floats are valid for any bit pattern
            }
        };
        alloc.init_mask().is_range_initialized(range).is_ok()
            && alloc.provenance().range_empty(range, &self.tcx)
            && alloc
                .get_bytes_unchecked(range)
                .chunks_exact(elem_ty.primitive_size(self.tcx).bytes_usize())
                .all(is_valid_elem)
    }

    /// Whether we view a value of the unsized type `ty` at the sized type it was unsized from: a
    /// slice or `dyn Trait` value is, and so is a `str` with `unsized_strings`.
    pub(crate) fn is_viewed_unsized_from(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            ty::Slice(_) | ty::Dynamic(..) => true,
            ty::Str => self.config.unsized_strings,
            _ => false,
        }
    }

    /// Express `place`, located `offset` bytes into `global`, as projections from the global, aiming
    /// for a place of the sized type `ty` if any. `in_bounds` tells whether that place is inside
    /// the global (incl. one past its end). Returns the type of the global, the projections and the
    /// type of the place they reach.
    fn place_in_global(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        place: &MPlaceTy<'tcx>,
        global: AllocTarget<'tcx>,
        offset: Size,
        in_bounds: bool,
        ty: Option<Ty<'tcx>>,
    ) -> InterpResult<'tcx, (Ty<'tcx>, ProjectionPath<'tcx>, Ty<'tcx>)> {
        let tcx = self.tcx;
        let ty = tcx.erase_and_anonymize_regions(ty);
        let size = match ecx.size_and_align_of_val(place)? {
            Some((size, _)) => size,
            None => Size::ZERO, // extern type
        };
        let decl_ty = match global {
            AllocTarget::Global(global) => tcx.erase_and_anonymize_regions(self.global_ty(global)),
            // Other allocations have no contents.
            _ => tcx.types.unit,
        };
        // We follow the structure of statics and of allocations we view at a type.
        let (path, end_ty) = if in_bounds && global.is_read_typed(&self.alloc_types) {
            let (prov, _) = place.ptr().into_raw_parts();
            let ptr = interpret::Pointer::new(prov, Size::ZERO);
            let base = ecx.ptr_to_mplace(ptr, ecx.layout_of(decl_ty)?);
            structural_path(ecx, base, offset, ty, size)
        } else {
            // The offset of a pointer outside of its allocation may be negative.
            let offset = tcx
                .data_layout
                .pointer_size()
                .sign_extend(offset.bytes().into());
            let proj = offset_projection(tcx, offset as i64, ty, size, in_bounds);
            let end_ty = match proj {
                Some((_, ty)) => ty,
                None => decl_ty,
            };
            (proj.into_iter().collect(), end_ty)
        };
        interp_ok((decl_ty, path, end_ty))
    }
}

/// The projection to the place located `offset` bytes after the current place, for a pointee of
/// size `size`, if `offset` isn't zero.
fn offset_projection<'tcx>(
    tcx: TyCtxt<'tcx>,
    offset: i64,
    ty: Option<Ty<'tcx>>,
    size: Size,
    in_bounds: bool,
) -> Option<(Projection<'tcx>, Ty<'tcx>)> {
    if offset == 0 {
        return None;
    }
    let size = size.bytes() as i64;
    let (count, elem_ty) = if let Some(ty) = ty
        && size != 0
        && offset % size == 0
    {
        (offset / size, Some(ty))
    } else {
        (offset, None)
    };
    let proj = Projection::Offset {
        count,
        ty: elem_ty,
        in_bounds,
    };
    Some((proj, ty.unwrap_or(tcx.types.u8)))
}

/// Find projections from `place` to the place of size `size` located `offset` bytes after it,
/// aiming for a place of type `to_ty` if any. There may be many ways of reaching the same
/// destination. Returns the projections to use, and the type of the final place, which may not
/// match `to_ty`, in which case a cast is needed.
fn structural_path<'tcx>(
    ecx: &CompileTimeInterpCx<'tcx>,
    mut place: MPlaceTy<'tcx>,
    mut offset: Size,
    to_ty: Option<Ty<'tcx>>,
    size: Size,
) -> (ProjectionPath<'tcx>, Ty<'tcx>) {
    let mut path = vec![];
    while !(Some(place.layout.ty) == to_ty && offset == Size::ZERO) {
        let Some((proj, sub, sub_offset)) = find_subplace(ecx, &place, offset, to_ty, size)
            .discard_err()
            .flatten()
        else {
            // Give up: we couldn't find a typed path, so we offset from the place we reached.
            let proj = offset_projection(*ecx.tcx, offset.bytes() as i64, to_ty, size, true);
            let end_ty = match proj {
                Some((_, ty)) => ty,
                None => place.layout.ty,
            };
            path.extend(proj);
            return (path, end_ty);
        };
        path.push((proj, sub.layout.ty));
        place = sub;
        offset = sub_offset;
    }
    (path, place.layout.ty)
}

/// Find the subplace of `place` that contains the place of size `size` (and type `to_ty`, if
/// known) located `offset` bytes after `place`. Returns the projection to that subplace, the
/// subplace, and the offset of the target within it.
fn find_subplace<'tcx>(
    ecx: &CompileTimeInterpCx<'tcx>,
    place: &MPlaceTy<'tcx>,
    offset: Size,
    to_ty: Option<Ty<'tcx>>,
    size: Size,
) -> InterpResult<'tcx, Option<(Projection<'tcx>, MPlaceTy<'tcx>, Size)>> {
    match place.layout.ty.kind() {
        ty::Array(elem, _) => {
            let len = place.len(ecx)?;
            let stride = place.layout.field(ecx, 0).size.bytes();
            let Some(i) = offset.bytes().checked_div(stride) else {
                return interp_ok(None);
            };
            // The target may be a subarray.
            if let Some(to_ty) = to_ty
                && let ty::Array(target_elem, _) = to_ty.kind()
                && target_elem == elem
                && offset.bytes().is_multiple_of(stride)
                && i + size.bytes() / stride <= len
            {
                let (from, to) = (i, i + size.bytes() / stride);
                let subslice = mir::ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: false,
                };
                let sub = ecx.project(place, subslice)?;
                return interp_ok(Some((Projection::Subslice { from, to }, sub, Size::ZERO)));
            }
            // The element that contains the target, if any.
            if i < len && offset.bytes() + size.bytes() <= (i + 1) * stride {
                let sub_offset = offset - Size::from_bytes(i * stride);
                let sub = ecx.project_index(place, i)?;
                return interp_ok(Some((Projection::Index(i), sub, sub_offset)));
            }
        }
        // Any field of a union contains the target, so we take the one of the right type if any.
        ty::Adt(adt_def, _) if adt_def.is_union() => {
            if offset == Size::ZERO
                && let Some(i) = (0..place.layout.fields.count())
                    .find(|&i| Some(place.layout.field(ecx, i).ty) == to_ty)
            {
                let field = FieldIdx::from_usize(i);
                let sub = ecx.project_field(place, field)?;
                return interp_ok(Some((Projection::Field(None, field), sub, offset)));
            }
        }
        ty::Adt(..) | ty::Tuple(..) | ty::Closure(..) => {
            let (place, variant) = match place.layout.ty.kind() {
                ty::Adt(adt_def, _) if adt_def.is_enum() => {
                    let variant = ecx.read_discriminant(place)?;
                    (ecx.project_downcast(place, variant)?, Some(variant))
                }
                _ => (place.clone(), None),
            };
            let FieldsShape::Arbitrary {
                offsets,
                in_memory_order,
            } = &place.layout.fields
            else {
                return interp_ok(None);
            };
            // The field that contains the target, if any. We can do binary search,
            // since fields don't overlap.
            let candidates = in_memory_order
                .raw
                .partition_point(|&i| offsets[i] <= offset);
            let mut found: Option<FieldIdx> = None;
            for &i in in_memory_order.raw[..candidates].iter().rev() {
                let field_offset = offsets[i];
                let field_size = place.layout.field(ecx, i.as_usize()).size;
                if offset + size <= field_offset + field_size {
                    found = Some(found.map_or(i, |found| found.min(i)));
                }
                // The previous fields end at or before the start of this field, so they can only
                // contain the target if it is zero-sized and this field starts at it.
                if field_offset < offset || size != Size::ZERO {
                    break;
                }
            }
            if let Some(field) = found {
                let sub = ecx.project_field(&place, field)?;
                let proj = Projection::Field(variant, field);
                return interp_ok(Some((proj, sub, offset - offsets[field])));
            }
        }
        _ => {}
    }
    interp_ok(None)
}
