use crate::translate::translate_bodies::BodyTransCtx;

use super::translate_ctx::*;
use charon_lib::ast::*;
use hax_frontend_exporter as hax;

impl ItemTransCtx<'_, '_> {
    fn translate_drop_method_body(
        &mut self,
        span: Span,
        def: &hax::FullDef,
    ) -> Result<Result<Body, Opaque>, Error> {
        let (hax::FullDefKind::Adt { drop_glue, .. } | hax::FullDefKind::Closure { drop_glue, .. }) =
            def.kind()
        else {
            panic!("Unexpected def adt: {def:?}")
        };
        let Some(body) = drop_glue else {
            return Ok(Err(Opaque));
        };

        let mut bt_ctx = BodyTransCtx::new(self);
        Ok(match bt_ctx.translate_body(span, body, &def.source_text) {
            Ok(Ok(body)) => Ok(body),
            Ok(Err(Opaque)) => Err(Opaque),
            Err(_) => Err(Opaque),
        })
    }

    /// Construct the `Ty` corresponding to the current adt. The generics must be the generics for
    /// that def_id.
    fn adt_self_ty(&mut self, span: Span, def_id: &hax::DefId) -> Result<Ty, Error> {
        // The def_id must correspond to a type definition.
        let self_decl_id = self.register_type_decl_id(span, def_id);
        let self_ty = TyKind::Adt(TypeDeclRef {
            id: TypeId::Adt(self_decl_id),
            generics: Box::new(self.the_only_binder().params.identity_args()),
        })
        .into_ty();
        Ok(self_ty)
    }

    fn adt_drop_predicate(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
    ) -> Result<TraitDeclRef, Error> {
        let drop_trait = self.get_lang_item(rustc_hir::LangItem::Drop);
        let drop_trait = self.register_trait_decl_id(span, &drop_trait);

        let self_ty = self.adt_self_ty(span, def_id)?;
        let implemented_trait = TraitDeclRef {
            id: drop_trait,
            generics: Box::new(GenericArgs::new_types([self_ty.clone()].into())),
        };
        Ok(implemented_trait)
    }

    /// Given an item that is a closure, generate the `call_once`/`call_mut`/`call` method
    /// (depending on `target_kind`).
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_drop_method(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        let drop_impl_id = self.register_drop_trait_impl_id(span, def.def_id());

        self.translate_def_generics(span, def)?;

        let implemented_trait = self.adt_drop_predicate(span, def.def_id())?;
        let self_ty = implemented_trait.generics.types[0].clone();
        let impl_ref = TraitImplRef {
            id: drop_impl_id,
            generics: Box::new(self.the_only_binder().params.identity_args()),
        };

        let kind = ItemKind::TraitImpl {
            impl_ref,
            trait_ref: implemented_trait,
            item_name: TraitItemName("drop".to_owned()),
            reuses_default: false,
        };

        // Add the method lifetime generic.
        assert!(self.innermost_binder_mut().bound_region_vars.is_empty());
        let region_id = self
            .innermost_binder_mut()
            .push_bound_region(hax::BoundRegionKind::Anon);

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Err(Opaque)
        } else {
            self.translate_drop_method_body(span, def)?
        };

        let input = TyKind::Ref(
            Region::Var(DeBruijnVar::new_at_zero(region_id)),
            self_ty,
            RefKind::Mut,
        )
        .into_ty();
        let signature = FunSig {
            generics: self.into_generics(),
            is_unsafe: false,
            inputs: vec![input],
            output: Ty::mk_unit(),
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            signature,
            kind,
            is_global_initializer: None,
            body,
        })
    }

    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_drop_impl(
        mut self,
        impl_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;

        self.translate_def_generics(span, def)?;

        let implemented_trait = self.adt_drop_predicate(span, def.def_id())?;
        let drop_trait = implemented_trait.id;

        // Construct the method reference.
        let method_id = self.register_drop_method_id(span, def.def_id());
        let method_name = TraitItemName("drop".to_owned());
        let method_binder = {
            let mut method_params = GenericParams::empty();
            method_params
                .regions
                .push_with(|index| RegionVar { index, name: None });

            let generics = self
                .outermost_binder()
                .params
                .identity_args_at_depth(DeBruijnId::one())
                .concat(&method_params.identity_args_at_depth(DeBruijnId::zero()));
            Binder::new(
                BinderKind::TraitMethod(drop_trait, method_name.clone()),
                method_params,
                FunDeclRef {
                    id: method_id,
                    generics: Box::new(generics),
                },
            )
        };

        let parent_trait_refs = {
            let meta_sized_trait = self.get_lang_item(rustc_hir::LangItem::MetaSized);
            let meta_sized_trait = self.register_trait_decl_id(span, &meta_sized_trait);
            let self_ty = implemented_trait.generics.types[0].clone();
            [TraitRef::new_builtin(
                meta_sized_trait,
                self_ty,
                Default::default(),
            )]
            .into()
        };

        Ok(TraitImpl {
            def_id: impl_id,
            item_meta,
            impl_trait: implemented_trait,
            generics: self.into_generics(),
            methods: vec![(method_name, method_binder)],
            parent_trait_refs,
            type_clauses: Default::default(),
            consts: Default::default(),
            types: Default::default(),
        })
    }
}
