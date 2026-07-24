use rustc_middle::ty;

use super::translate_ctx::*;
use crate::hax;
use crate::hax::FullDefKind;
use crate::translate::translate_crate::TransItemSourceKind;
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
        let tref = self.translate_trait_proof(span, &trait_proof)?;
        let method_id = self.translate_drop_glue_method_id(
            &trait_proof.pred.hax_skip_binder_ref().def_id,
            tref.trait_id(),
        )?;
        let fn_ptr = FnPtr::new(
            FnPtrKind::Trait(tref, method_id),
            self.drop_glue_generic_args(),
        );
        Ok(fn_ptr)
    }

    fn translate_drop_glue_method_body(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
    ) -> Result<Body, Error> {
        let (hax::FullDefKind::Adt { .. } | hax::FullDefKind::Closure { .. }) = def.kind() else {
            return Ok(Body::Missing);
        };

        let body = def.this().drop_glue_shim(self.hax_state());
        Ok(self.translate_body(span, body, &def.source_text))
    }

    /// Translate the body of the fake `Destruct::drop_glue` method we're adding to the
    /// `Destruct` trait. It contains the drop glue for the type.
    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_drop_glue_method(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
        impl_kind: TraitImplSource,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        let borrow_region = self.drop_glue_region();

        let trait_pred = match def.kind() {
            // Charon-generated `Destruct` impl for an ADT.
            FullDefKind::Adt { destruct_impl, .. } | FullDefKind::Closure { destruct_impl, .. } => {
                assert_eq!(impl_kind, TraitImplSource::ImplicitDestruct);
                &destruct_impl.trait_pred
            }
            _ => unreachable!(),
        };

        let implemented_trait = self.translate_trait_predicate(span, trait_pred)?;
        let item_id: AssocItemId = self
            .translate_drop_glue_method_id(&trait_pred.trait_ref.def_id, implemented_trait.id)?
            .into();
        let self_ty = implemented_trait
            .self_ty(&self.t_ctx.translated)
            .unwrap()
            .clone();

        let signature = self.drop_glue_method_sig(self_ty.clone(), borrow_region);
        let src = {
            let mut impl_generics = self.the_only_binder().params.identity_args();
            impl_generics
                .regions
                .pop()
                .expect("drop glue method should have a borrow lifetime");
            let destruct_impl_id =
                self.register_item(span, def.this(), TransItemSourceKind::TraitImpl(impl_kind));
            let impl_ref = TraitImplRef {
                id: destruct_impl_id,
                generics: Box::new(impl_generics),
            };
            ItemSource::TraitImpl {
                impl_ref,
                trait_ref: implemented_trait,
                item_id,
                reuses_default: false,
            }
        };

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Body::Opaque
        } else {
            self.translate_drop_glue_method_body(span, def)?
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            signature: Box::new(signature),
            src,
            is_global_initializer: None,
            body,
        })
    }

    pub(crate) fn drop_glue_region(&self) -> Region {
        Region::Var(DeBruijnVar::new_at_zero(
            self.the_only_binder()
                .drop_glue_region
                .expect("drop glue item should have a borrow lifetime"),
        ))
    }

    pub(crate) fn drop_glue_generic_args(&mut self) -> GenericArgs {
        let mut generics = GenericArgs::empty();
        generics.regions.push(self.translate_erased_region());
        generics
    }

    pub(crate) fn drop_glue_params() -> GenericParams {
        let mut params = GenericParams::empty();
        params
            .regions
            .push_with(|index| RegionParam::new(index, None, Variance::Covariant));
        params
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
        let params = Self::drop_glue_params();
        let region = Region::Var(DeBruijnVar::new_at_zero(RegionId::ZERO));
        let self_ty = self_ty.move_under_binder();
        RegionBinder {
            regions: params.regions,
            skip_binder: self.drop_glue_method_sig(self_ty, region),
        }
    }

    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_implicit_destruct_impl(
        mut self,
        impl_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;

        let (FullDefKind::Adt { destruct_impl, .. } | FullDefKind::Closure { destruct_impl, .. }) =
            def.kind()
        else {
            unreachable!("{:?}", def.def_id())
        };
        let mut timpl = self.translate_virtual_trait_impl(impl_id, item_meta, destruct_impl)?;

        // Add the `drop_glue(&mut self)` method.
        let destruct_trait_id = timpl.impl_trait.id;
        let destruct_trait_def_id: &hax::DefId = &destruct_impl.trait_pred.trait_ref.def_id;
        let method_id =
            self.translate_drop_glue_method_id(destruct_trait_def_id, destruct_trait_id)?;
        let method_binder = {
            let fun_id = self.register_item(
                span,
                def.this(),
                TransItemSourceKind::DropGlueMethod(TraitImplSource::ImplicitDestruct),
            );
            let method_params = Self::drop_glue_params();
            let generics = self
                .outermost_binder()
                .params
                .identity_args_at_depth(DeBruijnId::one())
                .concat(&method_params.identity_args());
            Binder::new(
                BinderKind::TraitMethod(destruct_trait_id, method_id),
                method_params,
                FunDeclRef {
                    id: fun_id,
                    generics: Box::new(generics),
                },
            )
        };
        timpl.methods.set_slot_extend(method_id, method_binder);

        Ok(timpl)
    }
}
