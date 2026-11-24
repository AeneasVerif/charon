use rustc_middle::ty;

use super::translate_ctx::*;
use crate::hax;
use charon_lib::ast::*;

impl<'tcx> ItemTransCtx<'tcx, '_> {
    pub fn translate_drop_glue_method_id(
        &mut self,
        destruct_trait_def_id: &hax::DefId,
        destruct_trait_id: TraitDeclId,
    ) -> Result<TraitMethodId, Error> {
        self.register_assoc_items(destruct_trait_def_id, destruct_trait_id)?;
        let method_id = TraitMethodId::ZERO; // It's the only method
        Ok(method_id)
    }

    /// Translate a call to `drop_glue` for that type.
    pub fn translate_drop_glue_method_call(
        &mut self,
        span: Span,
        ty: ty::Ty<'tcx>,
    ) -> Result<FnPtr, Error> {
        let trait_proof = hax::solve_destruct(self.hax_state_with_id(), ty);
        let tref = self
            .translate_trait_proof(span, &trait_proof)?
            .no_bound_vars();
        let method_id = self.translate_drop_glue_method_id(
            &trait_proof.pred.hax_skip_binder_ref().def_id,
            tref.trait_id(),
        )?;
        let fn_ptr = FnPtr::new(
            FnPtrKind::Trait(tref, method_id),
            self.self_borrow_generic_args(),
        );
        Ok(fn_ptr)
    }

    pub(crate) fn translate_drop_glue_method_body(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
    ) -> Result<Body, Error> {
        let (hax::FullDefKind::Adt(_) | hax::FullDefKind::Closure(_)) = def.kind() else {
            return Ok(Body::Missing);
        };

        let body = def.drop_glue_shim(self.hax_state());
        Ok(self.translate_body(span, body, &def.source_text))
    }

    // Small helper to deduplicate. Generates the signature `&'a mut self_ty -> ()`.
    pub fn drop_glue_method_sig(&self, self_ty: Ty, region: Region) -> FunSig {
        let self_ref = TyKind::Ref(region, self_ty, RefKind::Mut).into_ty();
        FunSig {
            is_unsafe: true,
            abi: Abi::rust(),
            is_variadic: false,
            inputs: [self_ref].into(),
            output: Ty::mk_unit(),
        }
    }

    pub fn drop_glue_fn_ptr_sig(&self, self_ty: Ty) -> RegionBinder<FunSig> {
        let params = Self::self_borrow_params();
        let region = Region::Var(DeBruijnVar::new_at_zero(RegionId::ZERO));
        let self_ty = self_ty.move_under_binder();
        RegionBinder {
            regions: params.regions,
            outlives: params.outlives,
            skip_binder: self.drop_glue_method_sig(self_ty, region),
        }
    }
}
