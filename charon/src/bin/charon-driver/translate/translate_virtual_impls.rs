//! Virtual impls are trait impls that rustc considers to exist but which don't have a `DefId`. We generate
//! a `TraitImpl` and method ourselves, as if they had been normal source-code impls.
use super::translate_ctx::*;
use crate::hax;
use crate::translate::translate_crate::{TransItemSourceKind, VirtualImplKind};
use charon_lib::ast::*;

impl VirtualImplKind {
    pub fn virtual_trait(self) -> hax::VirtualTrait {
        match self {
            VirtualImplKind::Destruct => hax::VirtualTrait::Destruct,
            VirtualImplKind::Callable(ClosureKind::FnOnce) => hax::VirtualTrait::FnOnce,
            VirtualImplKind::Callable(ClosureKind::FnMut) => hax::VirtualTrait::FnMut,
            VirtualImplKind::Callable(ClosureKind::Fn) => hax::VirtualTrait::Fn,
            VirtualImplKind::Coroutine(CoroutineKind::Coroutine) => hax::VirtualTrait::Coroutine,
            VirtualImplKind::Coroutine(CoroutineKind::Async) => hax::VirtualTrait::Future,
            VirtualImplKind::Coroutine(CoroutineKind::Gen) => hax::VirtualTrait::Iterator,
            VirtualImplKind::Coroutine(CoroutineKind::AsyncGen) => hax::VirtualTrait::AsyncIterator,
        }
    }

    /// The number of late-bound lifetimes of the method we generate, which become extra lifetime
    /// parameters of that method. The first one, if any, is the borrow of `self`.
    pub fn method_regions(self) -> usize {
        match self {
            // `call_once(self, args...)`
            VirtualImplKind::Callable(ClosureKind::FnOnce) => 0,
            // `poll(self: Pin<&'a mut Self>, cx: &'b mut Context<'c>)`
            VirtualImplKind::Coroutine(CoroutineKind::Async | CoroutineKind::AsyncGen) => 3,
            // `fn(&self, args...)`
            _ => 1,
        }
    }

    /// The name of the method we generate.
    pub fn method_path_elem(self) -> PathElem {
        match self {
            VirtualImplKind::Destruct => {
                PathElem::Builtin(BuiltinPathElem::DropGlue, Disambiguator::ZERO)
            }
            VirtualImplKind::Callable(kind) => {
                PathElem::Ident(kind.method_name().into(), Disambiguator::ZERO)
            }
            VirtualImplKind::Coroutine(kind) => {
                PathElem::Ident(kind.method_name().into(), Disambiguator::ZERO)
            }
        }
    }
}

impl<'tcx> ItemTransCtx<'tcx, '_> {
    fn virtual_method_id(
        &mut self,
        kind: VirtualImplKind,
        vimpl: &hax::VirtualTraitImpl<'tcx>,
        trait_id: TraitDeclId,
    ) -> Result<TraitMethodId, Error> {
        match kind {
            // Destruct doesn't have a method but we give it a fake one.
            VirtualImplKind::Destruct => {
                self.translate_drop_glue_method_id(&vimpl.trait_pred.trait_ref.def_id, trait_id)
            }
            _ => self.translate_trait_method_id(trait_id, &vimpl.methods[0].def_id),
        }
    }

    fn virtual_method_sig(
        &mut self,
        kind: VirtualImplKind,
        span: Span,
        vimpl: &hax::VirtualTraitImpl<'tcx>,
        self_ty: Ty,
    ) -> Result<FunSig, Error> {
        Ok(match kind {
            // Destruct doesn't have a method but we give it a fake one.
            VirtualImplKind::Destruct => {
                self.drop_glue_method_sig(self_ty, self.self_borrow_region())
            }
            _ => {
                let method_regions = self
                    .the_only_binder()
                    .method_regions
                    .iter()
                    .map(|rid| Region::Var(DeBruijnVar::new_at_zero(*rid)))
                    .collect();
                self.translate_poly_fun_sig(span, &vimpl.methods[0].sig)?
                    .apply(method_regions)
            }
        })
    }

    fn virtual_method_body(
        &mut self,
        kind: VirtualImplKind,
        span: Span,
        def: &hax::FullDef<'tcx>,
        signature: &FunSig,
    ) -> Result<Body, Error> {
        match kind {
            VirtualImplKind::Destruct => self.translate_drop_glue_method_body(span, def),
            VirtualImplKind::Callable(target_kind) => {
                self.translate_callable_method_body(span, def, target_kind, signature)
            }
            VirtualImplKind::Coroutine(_) => Ok(self.translate_def_body(span, def)),
        }
    }

    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_virtual_impl(
        mut self,
        impl_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
        kind: VirtualImplKind,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;
        let vimpl = def.virtual_impl(self.hax_state(), kind.virtual_trait());
        let mut timpl = self.translate_virtual_trait_impl(
            impl_id,
            item_meta,
            def.this(),
            TransImplSource::Virtual(kind),
            vimpl,
        )?;

        // In mono mode trait decls have no methods except `Desctruct::drop_glue`
        if self.monomorphize() && kind != VirtualImplKind::Destruct {
            return Ok(timpl);
        }

        // Add the method we generate. It takes the impl generics, plus the late-bound lifetimes of
        // the method (see `method_regions`).
        let trait_id = timpl.impl_trait.id;
        let method_id = self.virtual_method_id(kind, vimpl, trait_id)?;
        let method_binder = {
            let fun_id =
                self.register_item(span, def.this(), TransItemSourceKind::VirtualMethod(kind));
            let method_params = TransItemSourceKind::VirtualMethod(kind).method_region_params();
            let generics = self
                .outermost_binder()
                .params
                .identity_args_at_depth(DeBruijnId::one())
                .concat(&method_params.identity_args());
            Binder::new(
                BinderKind::TraitMethod(trait_id, method_id),
                method_params,
                FunDeclRef {
                    id: fun_id,
                    generics: Box::new(generics),
                },
            )
        };
        timpl.methods.set_slot_extend(method_id, method_binder);

        // The other methods reuse the defaults of the trait.
        let self_predicate = TraitRef::new(
            TraitRefKind::TraitImpl(TraitImplRef {
                id: impl_id,
                generics: Box::new(self.the_only_binder().params.identity_args()),
            }),
            timpl.impl_trait.clone(),
        );
        let trait_def = self.poly_hax_def(&vimpl.trait_pred.trait_ref.def_id)?;
        let hax::FullDefKind::Trait(t) = trait_def.kind() else {
            unreachable!()
        };
        for assoc in t.items(self.hax_state()) {
            if !matches!(assoc.kind, hax::AssocKind::Fn { .. }) || !assoc.has_value {
                continue;
            }
            let method_id = self.translate_trait_method_id_no_enqueue(trait_id, &assoc.def_id)?;
            let Some(bound_fn_ref) = self.translate_default_method_impl(&self_predicate, method_id)
            else {
                continue;
            };
            self.register_method_impl(trait_id, method_id, bound_fn_ref.skip_binder.id);
            timpl.methods.set_slot_extend(method_id, bound_fn_ref);
        }

        Ok(timpl)
    }

    /// Translate the method we generate for a virtual impl.
    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_virtual_method(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
        kind: VirtualImplKind,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        let vimpl = def.virtual_impl(self.hax_state(), kind.virtual_trait());
        let trait_pred = &vimpl.trait_pred;
        let implemented_trait = self.translate_trait_predicate(span, trait_pred)?;
        let item_id = self.virtual_method_id(kind, vimpl, implemented_trait.id)?;
        let self_ty = implemented_trait
            .self_ty(&self.t_ctx.translated)
            .unwrap()
            .clone();
        let signature = self.virtual_method_sig(kind, span, vimpl, self_ty)?;

        let src = {
            let mut impl_generics = self.the_only_binder().params.identity_args();
            let impl_regions = impl_generics.regions.len() - kind.method_regions();
            impl_generics.regions.truncate(impl_regions);
            let impl_id = self.register_item(
                span,
                def.this(),
                TransItemSourceKind::TraitImpl(TransImplSource::Virtual(kind)),
            );
            FunSource::TraitImpl {
                impl_ref: TraitImplRef {
                    id: impl_id,
                    generics: Box::new(impl_generics),
                },
                trait_ref: implemented_trait,
                item_id,
                reuses_default: false,
            }
        };

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Body::Opaque
        } else {
            self.virtual_method_body(kind, span, def, &signature)?
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            signature: Box::new(signature),
            src,
            body,
        })
    }
}
