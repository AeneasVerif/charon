use super::translate_ctx::*;
use charon_lib::common::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::gast::*;
use charon_lib::ids::Vector;
use charon_lib::meta::ItemMeta;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::types::*;
use charon_lib::ullbc_ast as ast;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use std::collections::HashMap;
use std::sync::Arc;

/// The context in which we are translating a clause, used to generate the appropriate ids and
/// trait references.
pub(crate) enum PredicateLocation {
    /// We're translating the parent clauses of a trait.
    Parent(TraitDeclId),
    /// We're translating the item clauses of a trait.
    Item(TraitDeclId, TraitItemName),
    /// We're translating anything else.
    Base,
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Helper for [translate_trait_impl].
    ///
    /// Remark: the [decl_item] is the item from the trait declaration.
    fn translate_trait_refs_from_impl_trait_item(
        &mut self,
        trait_impl_def_id: DefId,
        rust_impl_trait_ref: &rustc_middle::ty::TraitRef<'tcx>,
        item_id: DefId,
    ) -> Result<Vec<TraitRef>, Error> {
        trace!(
            "- trait_impl_def_id: {:?}\n- rust_impl_trait_ref: {:?}\n- decl_item: {:?}",
            trait_impl_def_id,
            rust_impl_trait_ref,
            item_id
        );

        let tcx = self.t_ctx.tcx;
        let span = tcx.def_span(trait_impl_def_id);

        // Lookup the trait clauses and substitute - TODO: not sure about the substitution
        let subst = rust_impl_trait_ref.args;
        let bounds = tcx.item_bounds(item_id);
        let param_env = tcx.param_env(trait_impl_def_id);
        let bounds = tcx.instantiate_and_normalize_erasing_regions(subst, param_env, bounds);
        let erase_regions = false;

        // Solve the predicate bounds
        let mut trait_refs = Vec::new();
        for bound in bounds {
            if let rustc_middle::ty::ClauseKind::Trait(trait_pred) = bound.kind().skip_binder() {
                let trait_ref = bound.kind().rebind(trait_pred.trait_ref);
                let trait_ref = hax::solve_trait(&self.hax_state, trait_ref);
                let trait_ref = self.translate_trait_impl_expr(span, erase_regions, &trait_ref)?;
                if let Some(trait_ref) = trait_ref {
                    trait_refs.push(trait_ref);
                }
            }
        }

        // Return
        Ok(trait_refs)
    }
}

impl<'tcx, 'ctx> TranslateCtx<'tcx, 'ctx> {
    /// Remark: this **doesn't** register the def id (on purpose)
    pub(crate) fn translate_trait_item_name(
        &mut self,
        def_id: &hax::DefId,
    ) -> Result<TraitItemName, Error> {
        // Translate the name
        let name = self.hax_def_id_to_name(def_id)?;
        let (name, id) = name.name.last().unwrap().as_ident().unwrap();
        assert!(id.is_zero());
        Ok(TraitItemName(name.to_string()))
    }

    #[tracing::instrument(skip(self, rust_id, item_meta))]
    pub fn translate_trait_decl(
        &mut self,
        def_id: TraitDeclId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TraitDecl, Error> {
        use hax::AssocKind;
        trace!("About to translate trait decl:\n{:?}", rust_id);
        trace!("Trait decl id:\n{:?}", def_id);

        let span = item_meta.span.rust_span();
        let erase_regions = false;
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        if let hax::FullDefKind::TraitAlias { .. } = def.kind() {
            error_or_panic!(self, span, &format!("Trait aliases are not supported"));
        }

        let hax::FullDefKind::Trait { items, .. } = &def.kind else {
            error_or_panic!(self, span, &format!("Unexpected definition: {def:?}"));
        };
        let items: Vec<(TraitItemName, &hax::AssocItem, Option<Arc<hax::FullDef>>)> = items
            .iter()
            .map(|item| {
                let name = TraitItemName(item.name.clone());
                // Warning: don't call `hax_def` on associated functions because this triggers
                // hax crashes on functions with higher-kinded predicates like
                // `Iterator::scan`.
                let def = if matches!(item.kind, AssocKind::Type | AssocKind::Const) {
                    let def = bt_ctx.t_ctx.hax_def(&item.def_id);
                    Some(def)
                } else {
                    None
                };
                (name, item, def)
            })
            .collect_vec();

        // Translate the generics
        bt_ctx.push_generics_for_def(span, def)?;

        // Gather the associated type clauses
        let mut type_clauses = Vec::new();
        for (name, item, def) in &items {
            match &item.kind {
                AssocKind::Type => {
                    let hax::FullDefKind::AssocTy { predicates, .. } =
                        &def.as_deref().unwrap().kind
                    else {
                        unreachable!()
                    };
                    // TODO: handle generics (i.e. GATs).
                    // Register the trait clauses as item trait clauses
                    bt_ctx.translate_predicates(
                        &predicates,
                        PredicateOrigin::TraitItem(name.clone()),
                        &PredicateLocation::Item(def_id, name.clone()),
                    )?;
                    if let Some(clauses) = bt_ctx.item_trait_clauses.get(name) {
                        type_clauses.push((name.clone(), clauses.clone()));
                    }
                }
                AssocKind::Fn => {}
                AssocKind::Const => {}
            }
        }

        // Note that in the generics returned by [get_generics], the trait refs only contain the
        // local trait clauses. The parent clauses are stored in `bt_ctx.parent_trait_clauses`.
        // TODO: Distinguish between required and implied trait clauses?
        let generics = bt_ctx.get_generics();

        // Translate the associated items
        // We do something subtle here: TODO: explain
        let mut consts = Vec::new();
        let mut const_defaults = HashMap::new();
        let mut types = Vec::new();
        let mut type_defaults = HashMap::new();
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();
        for (item_name, hax_item, opt_hax_def) in &items {
            let rust_item_id = DefId::from(&hax_item.def_id);
            let item_span = bt_ctx.t_ctx.tcx.def_span(rust_item_id);
            match &hax_item.kind {
                AssocKind::Fn => {
                    if hax_item.has_value {
                        // This is a *provided* method,
                        // Hack: To avoid having a trait that lists methods that aren't translated,
                        // we filter out invisible methods early. FIXME: remove this once we can
                        // translate all `Iterator` method signatures.
                        let fun_name = bt_ctx.t_ctx.def_id_to_name(rust_item_id)?;
                        if !bt_ctx.t_ctx.opacity_for_name(&fun_name).is_invisible() {
                            let fun_id = bt_ctx.register_fun_decl_id(item_span, rust_item_id);
                            provided_methods.push((item_name.clone(), fun_id));
                        }
                    } else {
                        // This is a required method (no default implementation)
                        let fun_id = bt_ctx.register_fun_decl_id(item_span, rust_item_id);
                        required_methods.push((item_name.clone(), fun_id));
                    }
                }
                AssocKind::Const => {
                    // Check if the constant has a value (i.e., a body).
                    // We are handling a trait *declaration* so we need to
                    // check whether the constant has a default value.
                    let hax::FullDefKind::AssocConst { ty, .. } =
                        &opt_hax_def.as_deref().unwrap().kind
                    else {
                        unreachable!()
                    };
                    if hax_item.has_value {
                        // The parameters of the constant are the same as those of the item that
                        // declares them.
                        let gref = GlobalDeclRef {
                            id: bt_ctx.register_global_decl_id(item_span, rust_item_id),
                            generics: generics.identity_args(),
                        };
                        const_defaults.insert(item_name.clone(), gref);
                    };
                    let ty = bt_ctx.translate_ty(item_span, erase_regions, ty)?;
                    consts.push((item_name.clone(), ty));
                }
                AssocKind::Type => {
                    let hax::FullDefKind::AssocTy { value, .. } =
                        &opt_hax_def.as_deref().unwrap().kind
                    else {
                        unreachable!()
                    };
                    if let Some(ty) = value {
                        let ty = bt_ctx.translate_ty(item_span, erase_regions, &ty)?;
                        type_defaults.insert(item_name.clone(), ty);
                    };
                    types.push(item_name.clone());
                }
            }
        }

        // Debugging:
        {
            let ctx = bt_ctx.into_fmt();
            let clauses = bt_ctx
                .trait_clauses_map
                .values()
                .flat_map(|x| x)
                .map(|c| c.fmt_with_ctx(&ctx))
                .collect::<Vec<String>>()
                .join("\n");
            let generic_clauses = generics
                .trait_clauses
                .iter()
                .map(|c| c.fmt_with_ctx(&ctx))
                .collect::<Vec<String>>()
                .join("\n");
            trace!(
                "Trait decl: {:?}:\n- all clauses:\n{}\n- generic.trait_clauses:\n{}\n",
                def_id,
                clauses,
                generic_clauses
            );
        }
        if item_meta.opacity.is_opaque() {
            let ctx = bt_ctx.into_fmt();
            bt_ctx.t_ctx.errors.dcx.span_warn(
                item_meta.span,
                format!(
                    "Trait declarations cannot be \"opaque\"; the trait `{}` will be translated as normal.",
                    item_meta.name.fmt_with_ctx(&ctx)
                ),
            )
        }
        // In case of a trait implementation, some values may not have been
        // provided, in case the declaration provided default values. We
        // check those, and lookup the relevant values.
        Ok(ast::TraitDecl {
            def_id,
            item_meta,
            generics,
            parent_clauses: bt_ctx.parent_trait_clauses,
            type_clauses,
            consts,
            const_defaults,
            types,
            type_defaults,
            required_methods,
            provided_methods,
        })
    }

    #[tracing::instrument(skip(self, rust_id, item_meta))]
    pub fn translate_trait_impl(
        &mut self,
        def_id: TraitImplId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<TraitImpl, Error> {
        trace!("About to translate trait impl:\n{:?}", rust_id);
        trace!("Trait impl id:\n{:?}", def_id);

        let tcx = self.tcx;
        let span = item_meta.span.rust_span();
        let erase_regions = false;
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        bt_ctx.push_generics_for_def(span, def)?;
        let generics = bt_ctx.get_generics();

        let hax::FullDefKind::Impl {
            impl_subject: hax::ImplSubject::Trait(trait_pred),
            items: impl_items,
            ..
        } = &def.kind
        else {
            unreachable!()
        };
        let implemented_trait_id = &trait_pred.trait_ref.def_id;
        let trait_def = bt_ctx.t_ctx.hax_def(implemented_trait_id);
        let hax::FullDefKind::Trait {
            items: decl_items, ..
        } = trait_def.kind()
        else {
            unreachable!()
        };

        // Retrieve the information about the implemented trait.
        let trait_id = bt_ctx.register_trait_decl_id(span, implemented_trait_id);
        let implemented_trait = {
            let implemented_trait = &trait_pred.trait_ref;
            let (regions, types, const_generics) = bt_ctx.translate_substs(
                span,
                erase_regions,
                None,
                &implemented_trait.generic_args,
            )?;
            let generics = GenericArgs {
                regions,
                types,
                const_generics,
                trait_refs: Vector::new(),
            };
            TraitDeclRef { trait_id, generics }
        };

        // Compute the parent trait references.
        let (
            rust_implemented_trait_ref,
            // [parent_trait_refs]: the trait refs which implement the parent
            // clauses of the implemented trait decl.
            parent_trait_refs,
        ) = {
            // TODO: what is below duplicates a bit [add_trait_impl_self_trait_clause]
            let rustc_middle::ty::ImplSubject::Trait(rust_trait_ref) =
                tcx.impl_subject(rust_id).instantiate_identity()
            else {
                unreachable!()
            };
            let parent_trait_refs = hax::solve_item_traits(
                &bt_ctx.hax_state,
                rust_trait_ref.def_id,
                rust_trait_ref.args,
                None,
            );
            let parent_trait_refs =
                bt_ctx.translate_trait_impl_exprs(span, erase_regions, &parent_trait_refs)?;

            (rust_trait_ref, parent_trait_refs)
        };

        {
            // Debugging
            let ctx = bt_ctx.into_fmt();
            let refs = parent_trait_refs
                .iter()
                .map(|c| c.fmt_with_ctx(&ctx))
                .collect::<Vec<String>>()
                .join("\n");
            trace!("Trait impl: {:?}\n- parent_trait_refs:\n{}", rust_id, refs);
        }

        // Explore the associated items
        // We do something subtle here: TODO
        let tcx = bt_ctx.t_ctx.tcx;
        let mut consts = HashMap::new();
        let mut types: HashMap<TraitItemName, Ty> = HashMap::new();
        let mut methods = HashMap::new();

        for item in impl_items {
            let name = TraitItemName(item.name.clone());
            let rust_item_id = DefId::from(&item.def_id);
            let item_span = tcx.def_span(rust_item_id);
            match &item.kind {
                hax::AssocKind::Fn => {
                    let fun_id = bt_ctx.register_fun_decl_id(item_span, rust_item_id);
                    methods.insert(name, fun_id);
                }
                hax::AssocKind::Const => {
                    // The parameters of the constant are the same as those of the item that
                    // declares them.
                    let gref = GlobalDeclRef {
                        id: bt_ctx.register_global_decl_id(item_span, rust_item_id),
                        generics: generics.identity_args(),
                    };
                    consts.insert(name, gref);
                }
                hax::AssocKind::Type => {
                    // Warning: don't call `hax_def` on associated functions because this triggers
                    // hax crashes on functions with higher-kinded predicates like
                    // `Iterator::scan`.
                    let item_def = bt_ctx.t_ctx.hax_def(&item.def_id);
                    let hax::FullDefKind::AssocTy {
                        value: Some(ty), ..
                    } = item_def.kind()
                    else {
                        unreachable!()
                    };
                    let ty = bt_ctx.translate_ty(item_span, erase_regions, ty)?;
                    types.insert(name, ty);
                }
            }
        }

        // In case of a trait implementation, some values may not have been
        // provided, in case the declaration provided default values. We
        // check those, and lookup the relevant values.
        let partial_consts = consts;
        let partial_types = types;
        let mut consts = Vec::new();
        let mut type_clauses = Vec::new();
        let mut types: Vec<(TraitItemName, Ty)> = Vec::new();
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();

        for decl_item in decl_items {
            let item_def_id = (&decl_item.def_id).into();
            let item_span = tcx.def_span(item_def_id);
            let name = TraitItemName(decl_item.name.to_string());
            match &decl_item.kind {
                hax::AssocKind::Fn => {
                    if let Some(&fun_id) = methods.get(&name) {
                        // Check if we implement a required method or reimplement a provided
                        // method.
                        if decl_item.has_value {
                            provided_methods.push((name, fun_id));
                        } else {
                            required_methods.push((name, fun_id));
                        }
                    }
                }

                hax::AssocKind::Const => {
                    // Does the trait impl provide an implementation for this const?
                    let c = match partial_consts.get(&name) {
                        Some(c) => c.clone(),
                        None => {
                            // The item is not defined in the trait impl: the trait decl *must*
                            // define a default value.
                            // The parameters of the constant are the same as those of the item
                            // that declares them.
                            GlobalDeclRef {
                                id: bt_ctx.register_global_decl_id(item_span, item_def_id),
                                generics: implemented_trait.generics.clone(),
                            }
                        }
                    };
                    consts.push((name, c));
                }
                hax::AssocKind::Type => {
                    // Does the trait impl provide an implementation for this type?
                    let ty = match partial_types.get(&name) {
                        Some(ty) => ty.clone(),
                        None => {
                            // The item is not defined in the trait impl: the trait decl *must*
                            // define a default value.
                            let ty = tcx
                                .type_of(item_def_id)
                                .instantiate(tcx, rust_implemented_trait_ref.args)
                                .sinto(&bt_ctx.hax_state);
                            bt_ctx.translate_ty(item_span, erase_regions, &ty)?
                        }
                    };
                    types.push((name.clone(), ty));

                    // Retrieve the trait refs
                    let trait_refs = bt_ctx.translate_trait_refs_from_impl_trait_item(
                        rust_id,
                        &rust_implemented_trait_ref,
                        item_def_id,
                    )?;
                    type_clauses.push((name, trait_refs));
                }
            }
        }
        if item_meta.opacity.is_opaque() {
            let ctx = bt_ctx.into_fmt();
            bt_ctx.t_ctx.errors.dcx.span_warn(
                item_meta.span,
                format!(
                    "Trait implementations cannot be \"opaque\"; the impl `{}` will be translated as normal.",
                    item_meta.name.fmt_with_ctx(&ctx)
                ),
            )
        }

        Ok(ast::TraitImpl {
            def_id,
            item_meta,
            impl_trait: implemented_trait,
            generics,
            parent_trait_refs,
            type_clauses,
            consts,
            types,
            required_methods,
            provided_methods,
        })
    }
}
