//! Reading pointers out of const-eval memory.
use crate::*;
use rustc_abi::Size;
use rustc_const_eval::const_eval::CompileTimeInterpCx;
use rustc_const_eval::interpret::{InterpResult, OpTy, Projectable, interp_ok};

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

        let target = match view_ty {
            Some(view_ty) => {
                let layout = ecx.layout_of(view_ty)?;
                if offset == Size::ZERO
                    && let AllocTarget::Global(global) = self.alloc_target(alloc_id)
                    && self.is_named_global(global)
                    // TODO: A view over an anonymous allocation must cover exactly the whole
                    // allocation. Our constant pointers don't have a way to indicate their offset,
                    // so if there's a mismatch it would be wrong.
                    && (matches!(global, GlobalRef::Static(_))
                        || layout.size == ecx.get_alloc_info(alloc_id).size)
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
                        place.offset(Size::ZERO, layout, ecx)?
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
}
