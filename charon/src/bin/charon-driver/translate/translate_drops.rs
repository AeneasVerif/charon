use rustc_middle::ty;

use super::translate_ctx::*;
use crate::hax;
use crate::hax::FullDefKind;
use crate::translate::translate_crate::TransItemSourceKind;
use charon_lib::{ast::*, formatter::IntoFormatter, pretty::FmtWithCtx};

impl<'tcx> ItemTransCtx<'tcx, '_> {
    /// Translate a call to `drop_in_place` for that type.
    pub fn translate_drop_in_place_method_call(
        &mut self,
        span: Span,
        ty: ty::Ty<'tcx>,
    ) -> Result<FnPtr, Error> {
        let impl_expr = hax::solve_destruct(self.hax_state_with_id(), ty);
        let tref = self.translate_trait_impl_expr(span, &impl_expr)?;
        let method_id = self.register_item(
            span,
            impl_expr.r#trait.hax_skip_binder_ref(),
            TransItemSourceKind::DropInPlaceMethod(None),
        );
        let fn_ptr = FnPtr {
            kind: Box::new(FnPtrKind::Trait(
                tref,
                TraitItemName("drop_in_place".into()),
                method_id,
            )),
            generics: Box::new(GenericArgs::empty()),
        };
        Ok(fn_ptr)
    }

    fn translate_drop_in_place_method_body(
        &mut self,
        span: Span,
        def: &hax::FullDef,
        self_ty: &Ty,
    ) -> Result<Body, Error> {
        let (hax::FullDefKind::Adt { .. } | hax::FullDefKind::Closure { .. }) = def.kind() else {
            return Ok(Body::Missing);
        };

        // Drop elaboration does not handle generics correctly, so it can ICE on some types. To be
        // safe we don't translate drop glue for poly types unless explicitly opted-in.
        let translate_glue = self.options.translate_poly_drop_glue
            || self.monomorphize()
            || def
                .this
                .def_id
                .underlying_rust_def_id()
                .is_none_or(|def_id| self.tcx.generics_of(def_id).is_empty());
        if !translate_glue {
            return Ok(Body::Missing);
        }

        let body = {
            let ctx = std::panic::AssertUnwindSafe(&mut *self);
            let def = std::panic::AssertUnwindSafe(def);
            // This is likely to panic, see the docs of `--precise-drops`.
            let Ok(body) =
                std::panic::catch_unwind(move || def.this().drop_glue_shim(ctx.hax_state()))
            else {
                let self_ty_name = if let TyKind::Adt(TypeDeclRef {
                    id: TypeId::Adt(type_id),
                    ..
                }) = self_ty.kind()
                    && let Some(name) = self.translated.item_name(*type_id)
                {
                    name.to_string_with_ctx(&self.into_fmt())
                } else {
                    "crate::the::Type".to_string()
                };
                raise_error!(
                    self,
                    span,
                    "rustc panicked while retrieving drop glue. \
                        This is known to happen with `--precise-drops`; to silence this warning, \
                        pass `--opaque '{{impl core::marker::Destruct for {}}}'` to charon",
                    self_ty_name
                )
            };
            body
        };

        Ok(self.translate_body(span, body, &def.source_text))
    }

    /// Translate the body of the fake `Destruct::drop_in_place` method we're adding to the
    /// `Destruct` trait. It contains the drop glue for the type.
    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_drop_in_place_method(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
        impl_kind: Option<TraitImplSource>,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;

        let trait_pred = match def.kind() {
            // Charon-generated `Destruct` impl for an ADT.
            FullDefKind::Adt { destruct_impl, .. } | FullDefKind::Closure { destruct_impl, .. } => {
                assert_eq!(impl_kind, Some(TraitImplSource::ImplicitDestruct));
                &destruct_impl.trait_pred
            }
            // The declaration of the method.
            FullDefKind::Trait { self_predicate, .. } => {
                assert_eq!(impl_kind, None);
                self_predicate
            }
            _ => unreachable!(),
        };

        let implemented_trait = self.translate_trait_predicate(span, trait_pred)?;
        let item_name = TraitItemName("drop_in_place".into());
        let self_ty = implemented_trait
            .self_ty(&self.t_ctx.translated)
            .unwrap()
            .clone();

        let src = match impl_kind {
            Some(impl_kind) => {
                let destruct_impl_id =
                    self.register_item(span, def.this(), TransItemSourceKind::TraitImpl(impl_kind));
                let impl_ref = TraitImplRef {
                    id: destruct_impl_id,
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
            Body::Opaque
        } else {
            self.translate_drop_in_place_method_body(span, def, &self_ty)?
        };

        let input = TyKind::RawPtr(self_ty, RefKind::Mut).into_ty();
        let signature = FunSig {
            is_unsafe: true,
            inputs: vec![input],
            output: Ty::mk_unit(),
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            signature,
            src,
            is_global_initializer: None,
            body,
        })
    }

    // Small helper to deduplicate.
    pub fn prepare_drop_in_place_method(
        &mut self,
        def: &hax::FullDef,
        span: Span,
        destruct_trait_id: TraitDeclId,
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
                BinderKind::TraitMethod(destruct_trait_id, method_name),
                GenericParams::empty(),
                FunDeclRef {
                    id: method_id,
                    generics: Box::new(generics),
                },
            )
        };
        (method_name, method_binder)
    }

    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_implicit_destruct_impl(
        mut self,
        impl_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;

        let (FullDefKind::Adt { destruct_impl, .. } | FullDefKind::Closure { destruct_impl, .. }) =
            def.kind()
        else {
            unreachable!("{:?}", def.def_id())
        };
        let mut timpl = self.translate_virtual_trait_impl(impl_id, item_meta, destruct_impl)?;

        // Add the `drop_in_place(*mut self)` method.
        timpl.methods.push(self.prepare_drop_in_place_method(
            def,
            span,
            timpl.impl_trait.id,
            Some(TraitImplSource::ImplicitDestruct),
        ));

        Ok(timpl)
    }
}
