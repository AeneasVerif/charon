use crate::translate::{translate_bodies::BodyTransCtx, translate_crate::TransItemSourceKind};

use super::translate_ctx::*;
use charon_lib::ast::{ullbc_ast_utils::BodyBuilder, *};
use hax::FullDefKind;

impl ItemTransCtx<'_, '_> {
    /// Translate the body of the fake `Drop::drop_in_place` method we're adding to the `Drop`
    /// trait. It contains the drop glue for the type.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_empty_drop_method(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;

        self.translate_def_generics(span, def)?;

        let (FullDefKind::Adt { drop_impl, .. } | FullDefKind::Closure { drop_impl, .. }) =
            def.kind()
        else {
            unreachable!()
        };
        let implemented_trait = self.translate_trait_predicate(span, &drop_impl.trait_pred)?;
        let self_ty = implemented_trait
            .self_ty(&self.t_ctx.translated)
            .unwrap()
            .clone();
        let drop_impl_id = self.register_item(
            span,
            def.this(),
            TransItemSourceKind::TraitImpl(TraitImplSource::ImplicitDrop),
        );
        let impl_ref = TraitImplRef {
            id: drop_impl_id,
            generics: Box::new(self.the_only_binder().params.identity_args()),
        };

        let src = ItemSource::TraitImpl {
            impl_ref,
            trait_ref: implemented_trait,
            item_name: TraitItemName("drop".into()),
            reuses_default: false,
        };

        // Add the method lifetime generic.
        assert!(self.innermost_binder_mut().bound_region_vars.is_empty());
        let region_id = self
            .innermost_binder_mut()
            .push_bound_region(hax::BoundRegionKind::Anon);

        let input = TyKind::Ref(
            Region::Var(DeBruijnVar::new_at_zero(region_id)),
            self_ty,
            RefKind::Mut,
        )
        .into_ty();
        let signature = FunSig {
            generics: self.into_generics(),
            is_unsafe: false,
            inputs: vec![input.clone()],
            output: Ty::mk_unit(),
        };

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Err(Opaque)
        } else {
            let mut builder = BodyBuilder::new(span, 1);
            let _ret = builder.new_var(None, Ty::mk_unit());
            let _self = builder.new_var(None, input);
            Ok(Body::Unstructured(builder.build()))
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            signature,
            src,
            is_global_initializer: None,
            body,
        })
    }

    fn translate_drop_in_place_method_body(
        &mut self,
        span: Span,
        def: &hax::FullDef,
    ) -> Result<Result<Body, Opaque>, Error> {
        let def = if let hax::FullDefKind::TraitImpl { trait_pred, .. } = def.kind()
            && let [hax::GenericArg::Type(self_ty)] = trait_pred.trait_ref.generic_args.as_slice()
            && let hax::TyKind::Adt(item) = self_ty.kind()
        {
            // `def` is a manual `impl Drop for Foo`. The requirements for such an impl are
            // stringent (https://doc.rust-lang.org/stable/error_codes/E0367.html); in particular
            // the impl generics must match the type generics exactly. Hence we can use the adt def
            // instead of the impl def, which would normally mess up generics.
            &self.hax_def(item)?
        } else {
            def
        };

        let (hax::FullDefKind::Adt { drop_glue, .. } | hax::FullDefKind::Closure { drop_glue, .. }) =
            def.kind()
        else {
            return Ok(Err(Opaque));
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

    /// Translate the body of the fake `Drop::drop_in_place` method we're adding to the `Drop`
    /// trait. It contains the drop glue for the type.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_drop_in_place_method(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
        impl_kind: Option<TraitImplSource>,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;

        self.translate_def_generics(span, def)?;

        let trait_pred = match def.kind() {
            // Normal `impl Drop for ...`.
            FullDefKind::TraitImpl { trait_pred, .. } => {
                assert_eq!(impl_kind, Some(TraitImplSource::Normal));
                trait_pred
            }
            // Charon-generated `Drop` impl for an ADT.
            FullDefKind::Adt { drop_impl, .. } | FullDefKind::Closure { drop_impl, .. } => {
                assert_eq!(impl_kind, Some(TraitImplSource::ImplicitDrop));
                &drop_impl.trait_pred
            }
            FullDefKind::Trait { self_predicate, .. } => {
                assert_eq!(impl_kind, None);
                self_predicate
            }
            _ => unreachable!(),
        };

        let implemented_trait = self.translate_trait_predicate(span, trait_pred)?;
        let item_name = TraitItemName("drop".into());
        let self_ty = implemented_trait
            .self_ty(&self.t_ctx.translated)
            .unwrap()
            .clone();

        let src = match impl_kind {
            Some(impl_kind) => {
                let drop_impl_id =
                    self.register_item(span, def.this(), TransItemSourceKind::TraitImpl(impl_kind));
                let impl_ref = TraitImplRef {
                    id: drop_impl_id,
                    generics: Box::new(self.the_only_binder().params.identity_args()),
                };
                ItemSource::TraitImpl {
                    impl_ref,
                    trait_ref: implemented_trait,
                    item_name,
                    reuses_default: false,
                }
            }
            None => ItemSource::TraitDecl {
                trait_ref: implemented_trait,
                item_name,
                has_default: false,
            },
        };

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Err(Opaque)
        } else {
            self.translate_drop_in_place_method_body(span, def)?
        };

        let input = TyKind::RawPtr(self_ty, RefKind::Mut).into_ty();
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
            src,
            is_global_initializer: None,
            body,
        })
    }

    // Small helper to deduplicate.
    pub fn prepare_drop_in_trait_method(
        &mut self,
        def: &hax::FullDef,
        span: Span,
        drop_trait_id: TraitDeclId,
        impl_kind: Option<TraitImplSource>,
    ) -> (TraitItemName, Binder<FunDeclRef>) {
        let method_id = self.register_item(
            span,
            def.this(),
            TransItemSourceKind::DropInPlaceMethod(impl_kind),
        );
        let method_name = TraitItemName("drop_in_place".into());
        let method_binder = {
            let generics = self
                .outermost_binder()
                .params
                .identity_args_at_depth(DeBruijnId::one());
            Binder::new(
                BinderKind::TraitMethod(drop_trait_id, method_name.clone()),
                GenericParams::empty(),
                FunDeclRef {
                    id: method_id,
                    generics: Box::new(generics),
                },
            )
        };
        (method_name, method_binder)
    }

    fn prepare_drop_method(
        &mut self,
        drop_trait_id: TraitDeclId,
        method_id: FunDeclId,
    ) -> (TraitItemName, Binder<FunDeclRef>) {
        let method_name = TraitItemName("drop".into());
        let method_binder = {
            let mut method_params = GenericParams::empty();
            method_params
                .regions
                .push_with(|index| RegionParam { index, name: None });

            let generics = self
                .outermost_binder()
                .params
                .identity_args_at_depth(DeBruijnId::one())
                .concat(&method_params.identity_args_at_depth(DeBruijnId::zero()));
            Binder::new(
                BinderKind::TraitMethod(drop_trait_id, method_name.clone()),
                method_params,
                FunDeclRef {
                    id: method_id,
                    generics: Box::new(generics),
                },
            )
        };
        (method_name, method_binder)
    }

    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_implicit_drop_impl(
        mut self,
        impl_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;

        self.translate_def_generics(span, def)?;

        let (FullDefKind::Adt { drop_impl, .. } | FullDefKind::Closure { drop_impl, .. }) =
            def.kind()
        else {
            unreachable!("{:?}", def.def_id())
        };
        let mut timpl = self.translate_virtual_trait_impl(impl_id, item_meta, drop_impl)?;

        // Add the `drop(&mut self)` method.
        let method_id = self.register_item(span, def.this(), TransItemSourceKind::EmptyDropMethod);
        timpl
            .methods
            .push(self.prepare_drop_method(timpl.impl_trait.id, method_id));

        // Add the `drop_in_place(*mut self)` method.
        timpl.methods.push(self.prepare_drop_in_trait_method(
            def,
            span,
            timpl.impl_trait.id,
            Some(TraitImplSource::ImplicitDrop),
        ));

        Ok(timpl)
    }
}
