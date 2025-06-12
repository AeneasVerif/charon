use super::translate_bodies::BodyTransCtx;
use super::translate_crate::TransItemSource;
use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::pretty::FmtWithCtx;
use derive_generic_visitor::Visitor;
use hax_frontend_exporter as hax;
use indexmap::IndexMap;
use itertools::Itertools;
use std::mem;
use std::ops::ControlFlow;
use std::sync::Arc;

impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    pub(crate) fn translate_item(&mut self, item_src: &TransItemSource) {
        let trans_id = self.id_map.get(&item_src).copied();
        let def_id = item_src.as_def_id();
        self.with_def_id(def_id, trans_id, |mut ctx| {
            let span = ctx.def_span(def_id);
            // Catch cycles
            let res = {
                // Stopgap measure because there are still many panics in charon and hax.
                let mut ctx = std::panic::AssertUnwindSafe(&mut ctx);
                std::panic::catch_unwind(move || ctx.translate_item_aux(item_src, trans_id))
            };
            match res {
                Ok(Ok(())) => return,
                // Translation error
                Ok(Err(_)) => {
                    register_error!(ctx, span, "Item `{def_id:?}` caused errors; ignoring.")
                }
                // Panic
                Err(_) => register_error!(
                    ctx,
                    span,
                    "Thread panicked when extracting item `{def_id:?}`."
                ),
            };
        })
    }

    pub(crate) fn translate_item_aux(
        &mut self,
        item_src: &TransItemSource,
        trans_id: Option<AnyTransId>,
    ) -> Result<(), Error> {
        // Translate the meta information
        let name = self.translate_name(item_src)?;
        if let Some(trans_id) = trans_id {
            self.translated.item_names.insert(trans_id, name.clone());
        }
        let opacity = self.opacity_for_name(&name);
        if opacity.is_invisible() {
            // Don't even start translating the item. In particular don't call `hax_def` on it.
            return Ok(());
        }
        let def = self.hax_def(item_src.as_def_id())?;
        let item_meta = self.translate_item_meta(&def, item_src, name, opacity);

        // Initialize the item translation context
        let bt_ctx = ItemTransCtx::new(def.def_id.clone(), trans_id, self);
        match item_src {
            TransItemSource::Type(_) => {
                let Some(AnyTransId::Type(id)) = trans_id else {
                    unreachable!()
                };
                let ty = bt_ctx.translate_type_decl(id, item_meta, &def)?;
                self.translated.type_decls.set_slot(id, ty);
            }
            TransItemSource::Fun(_) => {
                let Some(AnyTransId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl = bt_ctx.translate_function(id, item_meta, &def)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            TransItemSource::Global(_) => {
                let Some(AnyTransId::Global(id)) = trans_id else {
                    unreachable!()
                };
                let global_decl = bt_ctx.translate_global(id, item_meta, &def)?;
                self.translated.global_decls.set_slot(id, global_decl);
            }
            TransItemSource::TraitDecl(_) => {
                let Some(AnyTransId::TraitDecl(id)) = trans_id else {
                    unreachable!()
                };
                let trait_decl = bt_ctx.translate_trait_decl(id, item_meta, &def)?;
                self.translated.trait_decls.set_slot(id, trait_decl);
            }
            TransItemSource::TraitImpl(_) => {
                let Some(AnyTransId::TraitImpl(id)) = trans_id else {
                    unreachable!()
                };
                let trait_impl = bt_ctx.translate_trait_impl(id, item_meta, &def)?;
                self.translated.trait_impls.set_slot(id, trait_impl);
            }
            TransItemSource::ClosureTraitImpl(_, kind) => {
                let Some(AnyTransId::TraitImpl(id)) = trans_id else {
                    unreachable!()
                };
                let closure_trait_impl =
                    bt_ctx.translate_closure_trait_impl(id, item_meta, &def, *kind)?;
                self.translated.trait_impls.set_slot(id, closure_trait_impl);
            }
            TransItemSource::ClosureMethod(_, kind) => {
                let Some(AnyTransId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl = bt_ctx.translate_closure_method(id, item_meta, &def, *kind)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
        }
        Ok(())
    }
}

impl ItemTransCtx<'_, '_> {
    pub(crate) fn get_item_kind(
        &mut self,
        span: Span,
        def: &hax::FullDef,
    ) -> Result<ItemKind, Error> {
        let assoc = match def.kind() {
            hax::FullDefKind::AssocTy {
                associated_item, ..
            }
            | hax::FullDefKind::AssocConst {
                associated_item, ..
            }
            | hax::FullDefKind::AssocFn {
                associated_item, ..
            } => associated_item,
            hax::FullDefKind::Closure { args, .. } => {
                let info = self.translate_closure_info(span, args)?;
                return Ok(ItemKind::Closure { info });
            }
            _ => return Ok(ItemKind::TopLevel),
        };
        Ok(match &assoc.container {
            // E.g.:
            // ```
            // impl<T> List<T> {
            //   fn new() -> Self { ... } <- inherent method
            // }
            // ```
            hax::AssocItemContainer::InherentImplContainer { .. } => ItemKind::TopLevel,
            // E.g.:
            // ```
            // impl Foo for Bar {
            //   fn baz(...) { ... } // <- implementation of a trait method
            // }
            // ```
            hax::AssocItemContainer::TraitImplContainer {
                impl_id,
                impl_generics,
                impl_required_impl_exprs,
                implemented_trait_ref,
                implemented_trait_item,
                overrides_default,
                ..
            } => {
                let impl_id = self.register_trait_impl_id(span, impl_id);
                let impl_ref = TraitImplRef {
                    impl_id,
                    generics: Box::new(self.translate_generic_args(
                        span,
                        impl_generics,
                        impl_required_impl_exprs,
                        None,
                        GenericsSource::item(impl_id),
                    )?),
                };
                let trait_ref = self.translate_trait_ref(span, implemented_trait_ref)?;
                if matches!(def.kind(), hax::FullDefKind::AssocFn { .. }) {
                    // Ensure we translate the corresponding decl signature.
                    // FIXME(self_clause): also ensure we translate associated globals
                    // consistently; to do once we have clearer `Self` clause handling.
                    let _ = self.register_fun_decl_id(span, implemented_trait_item);
                }
                ItemKind::TraitImpl {
                    impl_ref,
                    trait_ref,
                    item_name: TraitItemName(assoc.name.clone()),
                    reuses_default: !overrides_default,
                }
            }
            // This method is the *declaration* of a trait item
            // E.g.:
            // ```
            // trait Foo {
            //   fn baz(...); // <- declaration of a trait method
            // }
            // ```
            hax::AssocItemContainer::TraitContainer { trait_ref, .. } => {
                // The trait id should be Some(...): trait markers (that we may eliminate)
                // don't have associated items.
                let trait_ref = self.translate_trait_ref(span, trait_ref)?;
                let item_name = TraitItemName(assoc.name.clone());
                ItemKind::TraitDecl {
                    trait_ref,
                    item_name,
                    has_default: assoc.has_value,
                }
            }
        })
    }

    /// Translate a type definition.
    ///
    /// Note that we translate the types one by one: we don't need to take into
    /// account the fact that some types are mutually recursive at this point
    /// (we will need to take that into account when generating the code in a file).
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_type_decl(
        mut self,
        trans_id: TypeDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TypeDecl, Error> {
        let span = item_meta.span;

        // Translate generics and predicates
        self.translate_def_generics(span, def)?;

        // Translate type body
        let kind = match &def.kind {
            _ if item_meta.opacity.is_opaque() => Ok(TypeDeclKind::Opaque),
            hax::FullDefKind::OpaqueTy | hax::FullDefKind::ForeignTy => Ok(TypeDeclKind::Opaque),
            hax::FullDefKind::TyAlias { ty, .. } => {
                // Don't error on missing trait refs.
                self.error_on_impl_expr_error = false;
                // We only translate crate-local type aliases so the `unwrap` is ok.
                let ty = ty.as_ref().unwrap();
                self.translate_ty(span, ty).map(TypeDeclKind::Alias)
            }
            hax::FullDefKind::Struct { def, .. }
            | hax::FullDefKind::Enum { def, .. }
            | hax::FullDefKind::Union { def, .. } => {
                self.translate_adt_def(trans_id, span, &item_meta, def)
            }
            hax::FullDefKind::Closure { args, .. } => {
                self.translate_closure_adt(trans_id, span, &args)
            }
            _ => panic!("Unexpected item when translating types: {def:?}"),
        };

        let kind = match kind {
            Ok(kind) => kind,
            Err(err) => TypeDeclKind::Error(err.msg),
        };
        let layout = self.translate_layout();
        let ptr_metadata = self.translate_ptr_metadata();
        let type_def = TypeDecl {
            def_id: trans_id,
            item_meta,
            generics: self.into_generics(),
            kind,
            layout,
            ptr_metadata,
        };

        Ok(type_def)
    }

    /// Translate one function.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_function(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<FunDecl, Error> {
        trace!("About to translate function:\n{:?}", def.def_id);
        let span = item_meta.span;

        // Translate the function signature
        trace!("Translating function signature");
        let signature = self.translate_function_signature(def, &item_meta)?;

        // Check whether this function is a method declaration for a trait definition.
        // If this is the case, it shouldn't contain a body.
        let kind = self.get_item_kind(span, def)?;
        let is_trait_method_decl_without_default = match &kind {
            ItemKind::TraitDecl { has_default, .. } => !has_default,
            _ => false,
        };

        let is_global_initializer = matches!(
            def.kind(),
            hax::FullDefKind::Const { .. }
                | hax::FullDefKind::AssocConst { .. }
                | hax::FullDefKind::AnonConst { .. }
                | hax::FullDefKind::InlineConst { .. }
                | hax::FullDefKind::PromotedConst { .. }
                | hax::FullDefKind::Static { .. }
        );
        let is_global_initializer =
            is_global_initializer.then(|| self.register_global_decl_id(span, &def.def_id));

        let body = if item_meta.opacity.with_private_contents().is_opaque()
            || is_trait_method_decl_without_default
        {
            Err(Opaque)
        } else if let hax::FullDefKind::Ctor {
            adt_def_id,
            ctor_of,
            variant_id,
            fields,
            output_ty,
            ..
        } = def.kind()
        {
            let body = self.build_ctor_body(
                span,
                &signature,
                adt_def_id,
                ctor_of,
                *variant_id,
                fields,
                output_ty,
            )?;
            Ok(body)
        } else {
            // Translate the body. This doesn't store anything if we can't/decide not to translate
            // this body.
            let mut bt_ctx = BodyTransCtx::new(&mut self);
            match bt_ctx.translate_def_body(item_meta.span, def) {
                Ok(Ok(body)) => Ok(body),
                // Opaque declaration
                Ok(Err(Opaque)) => Err(Opaque),
                // Translation error.
                // FIXME: handle error cases more explicitly.
                Err(_) => Err(Opaque),
            }
        };
        Ok(FunDecl {
            def_id,
            item_meta,
            signature,
            kind,
            is_global_initializer,
            body,
        })
    }

    /// Translate one global.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_global(
        mut self,
        def_id: GlobalDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<GlobalDecl, Error> {
        trace!("About to translate global:\n{:?}", def.def_id);
        let span = item_meta.span;

        // Translate the generics and predicates - globals *can* have generics
        // Ex.:
        // ```
        // impl<const N : usize> Foo<N> {
        //   const LEN : usize = N;
        // }
        // ```
        self.translate_def_generics(span, def)?;

        // Retrieve the kind
        let item_kind = self.get_item_kind(span, def)?;

        trace!("Translating global type");
        let ty = match &def.kind {
            hax::FullDefKind::Const { ty, .. }
            | hax::FullDefKind::AssocConst { ty, .. }
            | hax::FullDefKind::AnonConst { ty, .. }
            | hax::FullDefKind::InlineConst { ty, .. }
            | hax::FullDefKind::PromotedConst { ty, .. }
            | hax::FullDefKind::Static { ty, .. } => ty,
            _ => panic!("Unexpected def for constant: {def:?}"),
        };
        let ty = self.translate_ty(span, ty)?;

        let global_kind = match &def.kind {
            hax::FullDefKind::Static { .. } => GlobalKind::Static,
            hax::FullDefKind::Const { .. } | hax::FullDefKind::AssocConst { .. } => {
                GlobalKind::NamedConst
            }
            hax::FullDefKind::AnonConst { .. }
            | hax::FullDefKind::InlineConst { .. }
            | hax::FullDefKind::PromotedConst { .. } => GlobalKind::AnonConst,
            _ => panic!("Unexpected def for constant: {def:?}"),
        };

        let initializer = self.register_fun_decl_id(span, &def.def_id);

        Ok(GlobalDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            ty,
            kind: item_kind,
            global_kind,
            init: initializer,
        })
    }

    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_trait_decl(
        mut self,
        def_id: TraitDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TraitDecl, Error> {
        trace!("About to translate trait decl:\n{:?}", def.def_id);
        trace!("Trait decl id:\n{:?}", def_id);

        let span = item_meta.span;

        // Translate the generics
        // Note that in the generics returned by [translate_def_generics], the trait refs only
        // contain the local trait clauses. The parent clauses are stored in
        // `self.parent_trait_clauses`.
        self.translate_def_generics(span, def)?;

        if let hax::FullDefKind::TraitAlias { .. } = def.kind() {
            // Trait aliases don't have any items. Everything interesting is in the parent clauses.
            return Ok(TraitDecl {
                def_id,
                item_meta,
                parent_clauses: mem::take(&mut self.parent_trait_clauses),
                generics: self.into_generics(),
                type_clauses: Default::default(),
                consts: Default::default(),
                const_defaults: Default::default(),
                types: Default::default(),
                type_defaults: Default::default(),
                methods: Default::default(),
            });
        }

        let hax::FullDefKind::Trait {
            items,
            self_predicate,
            ..
        } = &def.kind
        else {
            raise_error!(self, span, "Unexpected definition: {def:?}");
        };
        let self_trait_ref = TraitRef {
            kind: TraitRefKind::SelfId,
            trait_decl_ref: RegionBinder::empty(
                self.translate_trait_predicate(span, self_predicate)?,
            ),
        };
        let items: Vec<(TraitItemName, &hax::AssocItem, Arc<hax::FullDef>)> = items
            .iter()
            .map(|(item, def)| {
                let name = TraitItemName(item.name.clone());
                (name, item, def.clone())
            })
            .collect_vec();

        // Translate the associated items
        // We do something subtle here: TODO: explain
        let mut consts = Vec::new();
        let mut const_defaults = IndexMap::new();
        let mut types = Vec::new();
        let mut type_clauses = Vec::new();
        let mut type_defaults = IndexMap::new();
        let mut methods = Vec::new();
        for (item_name, hax_item, hax_def) in &items {
            let item_def_id = &hax_item.def_id;
            let item_span = self.def_span(item_def_id);
            match &hax_def.kind {
                hax::FullDefKind::AssocFn { .. } => {
                    let fun_def = self.t_ctx.hax_def(item_def_id)?;
                    let binder_kind = BinderKind::TraitMethod(def_id, item_name.clone());
                    let fn_ref = self.translate_binder_for_def(
                        item_span,
                        binder_kind,
                        &fun_def,
                        |bt_ctx| {
                            // If the trait is opaque, we only translate the signature of a method
                            // with default body if it's overridden or used somewhere else.
                            // We insert the `Binder<FunDeclRef>` unconditionally here, and remove
                            // the ones that correspond to untranslated functions in the
                            // `remove_unused_methods` pass.
                            // FIXME: this triggers the translation of traits used in the method
                            // clauses, despite the fact that we may end up not needing them.
                            let fun_id = if bt_ctx.t_ctx.options.translate_all_methods
                                || item_meta.opacity.is_transparent()
                                || !hax_item.has_value
                            {
                                bt_ctx.register_fun_decl_id(item_span, item_def_id)
                            } else {
                                bt_ctx.register_fun_decl_id_no_enqueue(item_span, item_def_id)
                            };

                            assert_eq!(bt_ctx.binding_levels.len(), 2);
                            let mut fun_generics =
                                bt_ctx.outermost_binder().params.identity_args_at_depth(
                                    GenericsSource::item(def_id),
                                    DeBruijnId::one(),
                                );
                            // Add the necessary explicit `Self` clause at the start.
                            fun_generics.trait_refs.insert_and_shift_ids(
                                0.into(),
                                self_trait_ref.clone().move_under_binder(),
                            );
                            fun_generics = fun_generics.concat(
                                GenericsSource::item(fun_id),
                                &bt_ctx.innermost_binder().params.identity_args_at_depth(
                                    GenericsSource::Method(def_id.into(), item_name.clone()),
                                    DeBruijnId::zero(),
                                ),
                            );
                            Ok(FunDeclRef {
                                id: fun_id,
                                generics: Box::new(fun_generics),
                            })
                        },
                    )?;
                    methods.push((item_name.clone(), fn_ref));
                }
                hax::FullDefKind::AssocConst { ty, .. } => {
                    // Check if the constant has a value (i.e., a body).
                    if hax_item.has_value {
                        // The parameters of the constant are the same as those of the item that
                        // declares them.
                        let id = self.register_global_decl_id(item_span, item_def_id);
                        let generics_target = GenericsSource::item(id);
                        let mut generics =
                            self.the_only_binder().params.identity_args(generics_target);
                        generics.trait_refs.push(self_trait_ref.clone());
                        let gref = GlobalDeclRef {
                            id,
                            generics: Box::new(generics),
                        };
                        const_defaults.insert(item_name.clone(), gref);
                    };
                    let ty = self.translate_ty(item_span, ty)?;
                    consts.push((item_name.clone(), ty));
                }
                hax::FullDefKind::AssocTy { param_env, .. }
                    if !param_env.generics.params.is_empty() =>
                {
                    raise_error!(
                        self,
                        item_span,
                        "Generic associated types are not supported"
                    );
                }
                hax::FullDefKind::AssocTy { value, .. } => {
                    // TODO: handle generics (i.e. GATs).
                    if let Some(clauses) = self.item_trait_clauses.get(item_name) {
                        type_clauses.push((item_name.clone(), clauses.clone()));
                    }
                    if let Some(ty) = value {
                        let ty = self.translate_ty(item_span, &ty)?;
                        type_defaults.insert(item_name.clone(), ty);
                    };
                    types.push(item_name.clone());
                }
                _ => panic!("Unexpected definition for trait item: {hax_def:?}"),
            }
        }

        // In case of a trait implementation, some values may not have been
        // provided, in case the declaration provided default values. We
        // check those, and lookup the relevant values.
        Ok(TraitDecl {
            def_id,
            item_meta,
            parent_clauses: mem::take(&mut self.parent_trait_clauses),
            generics: self.into_generics(),
            type_clauses,
            consts,
            const_defaults,
            types,
            type_defaults,
            methods,
        })
    }

    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_trait_impl(
        mut self,
        def_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TraitImpl, Error> {
        trace!("About to translate trait impl:\n{:?}", def.def_id);
        trace!("Trait impl id:\n{:?}", def_id);

        let span = item_meta.span;

        self.translate_def_generics(span, def)?;

        if let hax::FullDefKind::TraitAlias { .. } = def.kind() {
            // Generate a blanket impl for this trait, as in:
            //   trait Alias<U> = Trait<Option<U>, Item = u32> + Clone;
            // becomes:
            //   trait Alias<U>: Trait<Option<U>, Item = u32> + Clone {}
            //   impl<U, Self: Trait<Option<U>, Item = u32> + Clone> Alias<U> for Self {}

            // `translate_def_generics` registers the clauses as implied clauses, but we want them
            // as required clauses for the impl.
            assert!(self.innermost_generics_mut().trait_clauses.is_empty());
            let clauses = mem::take(&mut self.parent_trait_clauses);
            self.innermost_generics_mut().trait_clauses = clauses;
            let trait_id = self.register_trait_decl_id(span, def.def_id());
            let mut generics = self
                .the_only_binder()
                .params
                .identity_args(GenericsSource::item(trait_id));
            // Do the inverse operation: the trait considers the clauses as implied.
            let parent_trait_refs = mem::take(&mut generics.trait_refs);
            let implemented_trait = TraitDeclRef {
                trait_id,
                generics: Box::new(generics),
            };
            let mut timpl = TraitImpl {
                def_id,
                item_meta,
                impl_trait: implemented_trait,
                generics: self.the_only_binder().params.clone(),
                parent_trait_refs,
                type_clauses: Default::default(),
                consts: Default::default(),
                types: Default::default(),
                methods: Default::default(),
            };
            // We got the predicates from a trait decl, so they may refer to the virtual `Self`
            // clause, which doesn't exist for impls. We fix that up here.
            {
                struct FixSelfVisitor {
                    binder_depth: DeBruijnId,
                }
                struct UnhandledSelf;
                impl Visitor for FixSelfVisitor {
                    type Break = UnhandledSelf;
                }
                impl VisitAstMut for FixSelfVisitor {
                    fn enter_region_binder<T: AstVisitable>(&mut self, _: &mut RegionBinder<T>) {
                        self.binder_depth = self.binder_depth.incr()
                    }
                    fn exit_region_binder<T: AstVisitable>(&mut self, _: &mut RegionBinder<T>) {
                        self.binder_depth = self.binder_depth.decr()
                    }
                    fn enter_binder<T: AstVisitable>(&mut self, _: &mut Binder<T>) {
                        self.binder_depth = self.binder_depth.incr()
                    }
                    fn exit_binder<T: AstVisitable>(&mut self, _: &mut Binder<T>) {
                        self.binder_depth = self.binder_depth.decr()
                    }
                    fn visit_trait_ref_kind(
                        &mut self,
                        kind: &mut TraitRefKind,
                    ) -> ControlFlow<Self::Break> {
                        match kind {
                            TraitRefKind::SelfId => return ControlFlow::Break(UnhandledSelf),
                            TraitRefKind::ParentClause(box TraitRefKind::SelfId, _, clause_id) => {
                                *kind = TraitRefKind::Clause(DeBruijnVar::bound(
                                    self.binder_depth,
                                    *clause_id,
                                ))
                            }
                            _ => (),
                        }
                        self.visit_inner(kind)
                    }
                }
                match timpl.drive_mut(&mut FixSelfVisitor {
                    binder_depth: DeBruijnId::zero(),
                }) {
                    ControlFlow::Continue(()) => {}
                    ControlFlow::Break(UnhandledSelf) => {
                        register_error!(
                            self,
                            span,
                            "Found `Self` clause we can't handle \
                             in a trait alias blanket impl."
                        );
                    }
                }
            };
            return Ok(timpl);
        }

        let hax::FullDefKind::TraitImpl {
            trait_pred,
            implied_impl_exprs,
            items: impl_items,
            ..
        } = &def.kind
        else {
            unreachable!()
        };

        // Retrieve the information about the implemented trait.
        let implemented_trait_id = &trait_pred.trait_ref.def_id;
        let trait_id = self.register_trait_decl_id(span, implemented_trait_id);
        let implemented_trait = {
            let implemented_trait = &trait_pred.trait_ref;
            let generics = self.translate_generic_args(
                span,
                &implemented_trait.generic_args,
                &[],
                None,
                GenericsSource::item(trait_id),
            )?;
            TraitDeclRef {
                trait_id,
                generics: Box::new(generics),
            }
        };
        // A `TraitRef` that points to this impl with the correct generics.
        let self_predicate = TraitRef {
            kind: TraitRefKind::TraitImpl(
                def_id,
                Box::new(
                    self.the_only_binder()
                        .params
                        .identity_args(GenericsSource::item(def_id)),
                ),
            ),
            trait_decl_ref: RegionBinder::empty(implemented_trait.clone()),
        };

        // The trait refs which implement the parent clauses of the implemented trait decl.
        let parent_trait_refs = self.translate_trait_impl_exprs(span, &implied_impl_exprs)?;

        {
            // Debugging
            let ctx = self.into_fmt();
            let refs = parent_trait_refs
                .iter()
                .map(|c| c.with_ctx(&ctx))
                .format("\n");
            trace!(
                "Trait impl: {:?}\n- parent_trait_refs:\n{}",
                def.def_id,
                refs
            );
        }

        // Explore the associated items
        let mut consts = Vec::new();
        let mut types: Vec<(TraitItemName, Ty)> = Vec::new();
        let mut methods = Vec::new();
        let mut type_clauses = Vec::new();

        for impl_item in impl_items {
            use hax::ImplAssocItemValue::*;
            let name = TraitItemName(impl_item.name.clone());
            let item_def = impl_item.def(); // The impl item or the corresponding trait default.
            let item_span = self.def_span(&item_def.def_id);
            let item_def_id = &item_def.def_id;
            match item_def.kind() {
                hax::FullDefKind::AssocFn { .. } => {
                    match &impl_item.value {
                        Provided { is_override, .. } => {
                            let fun_def = self.t_ctx.hax_def(item_def_id)?;
                            let binder_kind = BinderKind::TraitMethod(trait_id, name.clone());
                            let fn_ref = self.translate_binder_for_def(
                                item_span,
                                binder_kind,
                                &fun_def,
                                |bt_ctx| {
                                    // If the impl is opaque, we only translate the signature of a
                                    // method with a default body if it's directly used somewhere
                                    // else.
                                    // We insert the `Binder<FunDeclRef>` unconditionally here, and
                                    // remove the ones that correspond to untranslated functions in
                                    // the `remove_unused_methods` pass.
                                    let fun_id = if bt_ctx.t_ctx.options.translate_all_methods
                                        || item_meta.opacity.is_transparent()
                                        || !*is_override
                                    {
                                        bt_ctx.register_fun_decl_id(item_span, item_def_id)
                                    } else {
                                        bt_ctx
                                            .register_fun_decl_id_no_enqueue(item_span, item_def_id)
                                    };

                                    // TODO: there's probably a cleaner way to write this
                                    assert_eq!(bt_ctx.binding_levels.len(), 2);
                                    let fun_generics = bt_ctx
                                        .outermost_binder()
                                        .params
                                        .identity_args_at_depth(
                                            GenericsSource::item(def_id),
                                            DeBruijnId::one(),
                                        )
                                        .concat(
                                            GenericsSource::item(fun_id),
                                            &bt_ctx
                                                .innermost_binder()
                                                .params
                                                .identity_args_at_depth(
                                                    GenericsSource::Method(
                                                        trait_id.into(),
                                                        name.clone(),
                                                    ),
                                                    DeBruijnId::zero(),
                                                ),
                                        );
                                    Ok(FunDeclRef {
                                        id: fun_id,
                                        generics: Box::new(fun_generics),
                                    })
                                },
                            )?;
                            methods.push((name, fn_ref));
                        }
                        DefaultedFn { .. } => {
                            // TODO: handle defaulted methods
                        }
                        _ => unreachable!(),
                    }
                }
                hax::FullDefKind::AssocConst { .. } => {
                    let id = self.register_global_decl_id(item_span, item_def_id);
                    let generics_target = GenericsSource::item(id);
                    // The parameters of the constant are the same as those of the item that
                    // declares them.
                    let generics = match &impl_item.value {
                        Provided { .. } => {
                            self.the_only_binder().params.identity_args(generics_target)
                        }
                        _ => {
                            let mut generics = implemented_trait
                                .generics
                                .clone()
                                .with_target(generics_target);
                            generics.trait_refs.push(self_predicate.clone());
                            generics
                        }
                    };
                    let gref = GlobalDeclRef {
                        id,
                        generics: Box::new(generics),
                    };
                    consts.push((name, gref));
                }
                hax::FullDefKind::AssocTy { param_env, .. }
                    if !param_env.generics.params.is_empty() =>
                {
                    // We don't support GATs; the error was already reported in the trait declaration.
                }
                hax::FullDefKind::AssocTy { value, .. } => {
                    let ty = match &impl_item.value {
                        Provided { .. } => value.as_ref().unwrap(),
                        DefaultedTy { ty, .. } => ty,
                        _ => unreachable!(),
                    };
                    let ty = self.translate_ty(item_span, &ty)?;
                    types.push((name.clone(), ty));

                    let trait_refs =
                        self.translate_trait_impl_exprs(item_span, &impl_item.required_impl_exprs)?;
                    type_clauses.push((name, trait_refs));
                }
                _ => panic!("Unexpected definition for trait item: {item_def:?}"),
            }
        }

        Ok(TraitImpl {
            def_id,
            item_meta,
            impl_trait: implemented_trait,
            generics: self.into_generics(),
            parent_trait_refs,
            type_clauses,
            consts,
            types,
            methods,
        })
    }
}
