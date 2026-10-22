//! Reading pointers out of const-eval memory.
use crate::*;
use rustc_abi::{FieldIdx, FieldsShape, Size};
use rustc_const_eval::const_eval::CompileTimeInterpCx;
use rustc_const_eval::interpret::{InterpResult, MPlaceTy, OpTy, Projectable, interp_ok};

impl<'tcx> ConstReader<'tcx> {
    /// Read a reference or raw pointer. Pointers to globals that we name are kept as pointers to
    /// these globals, and we fall back to reading the pointee for other cases.
    pub(crate) fn read_pointer(
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
            let int = ecx.read_scalar(op)?.to_scalar_int()?;
            let kind = ConstKind::PtrNoProvenance(int.to_uint(int.size()));
            return interp_ok(Const {
                ty: op.layout.ty,
                kind,
            });
        };

        let ty = place.layout.ty;
        let unsize = if place.meta().has_meta() {
            let tail = tcx.struct_tail_for_codegen(ty, self.typing_env);
            let from = self.sized_tail(ecx, &place, tail)?;
            Some(Unsize { from, to: tail })
        } else {
            None
        };
        // A slice or `dyn Trait` value is viewed at the sized type it was unsized from. Other
        // unsized values (e.g. a `CStr`) have no such type: we read them at their unsized type.
        let view_ty = match ty.kind() {
            _ if place.layout.is_sized() => Some(ty),
            ty::Slice(_) | ty::Dynamic(..) => unsize.map(|unsize| unsize.from),
            _ => None,
        };

        let alloc_target = self.alloc_target(alloc_id);
        // A pointer outside of its allocation (one-past-the-end is fine) needs a wrapping offset.
        let in_bounds = offset <= ecx.get_alloc_info(alloc_id).size;
        let kind = if let Some(view_ty) = view_ty
            && match alloc_target {
                AllocTarget::Global(global) => {
                    self.is_named_global(global)
                        // We can't read the pointee of a pointer outside of its allocation, so we
                        // name the allocation even if we otherwise inline them.
                        || !in_bounds
                            && matches!(tcx.global_alloc(alloc_id), interpret::GlobalAlloc::Memory(_))
                }
                AllocTarget::Fn(_) => true,
                AllocTarget::VTable(..) | AllocTarget::TypeId(..) => false,
            }
            && let Some((decl_ty, projections, end_ty)) =
                self.place_in_global(ecx, &place, alloc_target, offset, in_bounds, view_ty)
        {
            let target = PtrTarget::Global {
                target: alloc_target,
                ty: decl_ty,
                projections,
            };
            if end_ty == tcx.erase_and_anonymize_regions(view_ty) {
                ConstKind::Ptr { target, unsize }
            } else {
                // Point to the place we reached, then cast the pointer to the right type.
                let (ty::Ref(.., mutability) | ty::RawPtr(_, mutability)) = *op.layout.ty.kind()
                else {
                    unreachable!()
                };
                let ptr = |ty, kind| Box::new(Const { ty, kind });
                let inner = ptr(
                    Ty::new_ptr(tcx, end_ty, mutability),
                    ConstKind::Ptr {
                        target,
                        unsize: None,
                    },
                );
                match unsize {
                    None => ConstKind::PtrCast {
                        ptr: inner,
                        unsize: None,
                    },
                    // Cast to the sized type first, then unsize.
                    Some(unsize) => ConstKind::PtrCast {
                        ptr: ptr(
                            Ty::new_ptr(tcx, view_ty, mutability),
                            ConstKind::PtrCast {
                                ptr: inner,
                                unsize: None,
                            },
                        ),
                        unsize: Some(unsize),
                    },
                }
            }
        } else if !in_bounds {
            ConstKind::Unsupported("pointer outside of its allocation")
        } else if let AllocTarget::VTable(..) = alloc_target {
            // A vtable has no global we can point into, and const-eval can't read its contents.
            ConstKind::Unsupported("pointer into a vtable")
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
        interp_ok(Const {
            ty: op.layout.ty,
            kind,
        })
    }

    /// Express the place of type `ty` located `offset` bytes into `global` (whose allocation
    /// `place` points into) as projections from the global. `in_bounds` tells whether that place
    /// is inside the global (incl. one past its end). Returns the type of the global, the
    /// projections and the type of the place they reach.
    fn place_in_global(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        place: &MPlaceTy<'tcx>,
        global: AllocTarget<'tcx>,
        offset: Size,
        in_bounds: bool,
        ty: Ty<'tcx>,
    ) -> Option<(Ty<'tcx>, ProjectionPath<'tcx>, Ty<'tcx>)> {
        let tcx = self.tcx;
        let ty = tcx.erase_and_anonymize_regions(ty);
        let size = ecx.layout_of(ty).ok()?.size;
        let decl_ty = match global {
            AllocTarget::Global(global) => tcx.erase_and_anonymize_regions(self.global_ty(global)),
            // Other allocations have no contents.
            _ => tcx.types.unit,
        };
        // Allocations without an item are untyped (see `global_ty`), so we only follow the
        // structure of statics. A place outside of the global has no such structure.
        let (path, end_ty) = if in_bounds && let AllocTarget::Global(GlobalRef::Static(_)) = global
        {
            let (prov, _) = place.ptr().into_raw_parts();
            let ptr = interpret::Pointer::new(prov, Size::ZERO);
            let base = ecx.ptr_to_mplace(ptr, ecx.layout_of(decl_ty).ok()?);
            structural_path(ecx, base, offset, ty, size)
        } else {
            // The offset of a pointer outside of its allocation may be negative.
            let offset = tcx
                .data_layout
                .pointer_size()
                .sign_extend(offset.bytes().into());
            let proj = offset_projection(offset as i64, ty, size, in_bounds);
            // An offset reaches a place of the type we want.
            let end_ty = if proj.is_some() { ty } else { decl_ty };
            (proj.map(|proj| (proj, ty)).into_iter().collect(), end_ty)
        };
        Some((decl_ty, path, end_ty))
    }
}

/// The projection to the place located `offset` bytes after the current place, for a pointee of
/// type `ty` and size `size`, if `offset` isn't zero.
fn offset_projection<'tcx>(
    offset: i64,
    ty: Ty<'tcx>,
    size: Size,
    in_bounds: bool,
) -> Option<Projection<'tcx>> {
    if offset == 0 {
        return None;
    }
    let size = size.bytes() as i64;
    let (count, ty) = if size != 0 && offset % size == 0 {
        (offset / size, Some(ty))
    } else {
        (offset, None)
    };
    Some(Projection::Offset {
        count,
        ty,
        in_bounds,
    })
}

/// Find projections from `place` to the place of type `to_ty` and size `size` located `offset`
/// bytes after it. There may be many ways of reaching the same destination. Returns the
/// projections to use, and the type of the final place, which may not match `to_ty`, in which
/// case a cast is needed.
fn structural_path<'tcx>(
    ecx: &CompileTimeInterpCx<'tcx>,
    mut place: MPlaceTy<'tcx>,
    mut offset: Size,
    to_ty: Ty<'tcx>,
    size: Size,
) -> (ProjectionPath<'tcx>, Ty<'tcx>) {
    let mut path = vec![];
    while !(place.layout.ty == to_ty && offset == Size::ZERO) {
        let Some((proj, sub, sub_offset)) = find_subplace(ecx, &place, offset, to_ty, size)
            .discard_err()
            .flatten()
        else {
            // Give up: we couldn't find a typed path, so we offset from the place we reached.
            let proj = offset_projection(offset.bytes() as i64, to_ty, size, true);
            let end_ty = if proj.is_some() {
                to_ty
            } else {
                place.layout.ty
            };
            path.extend(proj.map(|proj| (proj, to_ty)));
            return (path, end_ty);
        };
        path.push((proj, sub.layout.ty));
        place = sub;
        offset = sub_offset;
    }
    (path, to_ty)
}

/// Find the subplace of `place` that contains the place of type `to_ty` and size `size` located
/// `offset` bytes after `place`. Returns the projection to that subplace, the subplace, and the
/// offset of the target within it.
fn find_subplace<'tcx>(
    ecx: &CompileTimeInterpCx<'tcx>,
    place: &MPlaceTy<'tcx>,
    offset: Size,
    to_ty: Ty<'tcx>,
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
            if let ty::Array(target_elem, _) = to_ty.kind()
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
                    .find(|&i| place.layout.field(ecx, i).ty == to_ty)
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
