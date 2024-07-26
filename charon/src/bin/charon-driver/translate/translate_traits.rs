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
use hax_frontend_exporter::AssocItemContainer;
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
        decl_item: &rustc_middle::ty::AssocItem,
    ) -> Result<Vec<TraitRef>, Error> {
        trace!(
            "- trait_impl_def_id: {:?}\n- rust_impl_trait_ref: {:?}\n- decl_item: {:?}",
            trait_impl_def_id,
            rust_impl_trait_ref,
            decl_item
        );

        let tcx = self.t_ctx.tcx;
        let span = tcx.def_span(trait_impl_def_id);

        // Lookup the trait clauses and substitute - TODO: not sure about the substitution
        let subst = rust_impl_trait_ref.args;
        let bounds = tcx.item_bounds(decl_item.def_id);
        let param_env = tcx.param_env(trait_impl_def_id);
        let bounds = tcx.instantiate_and_normalize_erasing_regions(subst, param_env, bounds);
        let erase_regions = false;

        // Solve the predicate bounds
        let mut trait_refs = Vec::new();
        for bound in bounds {
            if let rustc_middle::ty::ClauseKind::Trait(trait_pred) = bound.kind().skip_binder() {
                let trait_ref = bound.kind().rebind(trait_pred.trait_ref);
                let trait_ref = hax::solve_trait(&self.hax_state, param_env, trait_ref);
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
        rust_id: DefId,
    ) -> Result<TraitItemName, Error> {
        // Translate the name
        let name = self.def_id_to_name(rust_id)?;
        let (name, id) = name.name.last().unwrap().as_ident();
        assert!(id.is_zero());
        Ok(TraitItemName(name.to_string()))
    }

    pub fn translate_trait_decl(
        &mut self,
        def_id: TraitDeclId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::Def,
    ) -> Result<TraitDecl, Error> {
        use hax::AssocKind;
        trace!("About to translate trait decl:\n{:?}", rust_id);
        trace!("Trait decl id:\n{:?}", def_id);

        let span = item_meta.span.rust_span();
        let erase_regions = false;
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);
        let tcx = bt_ctx.t_ctx.tcx;
        let name = bt_ctx.t_ctx.def_id_to_name(rust_id)?;

        let hax::Def::Trait { items, .. } = def else {
            panic!("Unexpected definition: {def:?}")
        };
        let items: Vec<(TraitItemName, &hax::AssocItem, Option<Arc<hax::Def>>)> = items
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
        bt_ctx.push_generics_for_def(span, rust_id, def)?;

        // Gather the associated type clauses
        let mut type_clauses = Vec::new();
        for (name, item, def) in &items {
            match &item.kind {
                AssocKind::Type => {
                    let hax::Def::AssocTy { predicates, .. } = def.as_deref().unwrap() else {
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
            let rust_item_id = (&hax_item.def_id).into();
            let item_span = tcx.def_span(rust_item_id);
            match &hax_item.kind {
                AssocKind::Fn => {
                    // Skip the provided methods for the *external* trait declarations,
                    // but still remember their name (unless `extract_opaque_bodies` is set).
                    // TODO: translate function signatures unconditionally.
                    if hax_item.has_value {
                        // This is a *provided* method
                        if rust_id.is_local() || bt_ctx.t_ctx.options.extract_opaque_bodies {
                            let fun_id = bt_ctx.register_fun_decl_id(item_span, rust_item_id);
                            provided_methods.push((item_name.clone(), Some(fun_id)));
                        } else {
                            provided_methods.push((item_name.clone(), None));
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
                    let Some(hax::Def::AssocConst { ty, .. }) = opt_hax_def.as_deref() else {
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
                    let Some(hax::Def::AssocTy { value, .. }) = opt_hax_def.as_deref() else {
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
                .trait_clauses
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
                    name.fmt_with_ctx(&ctx)
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

    pub fn translate_trait_impl(
        &mut self,
        def_id: TraitImplId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::Def,
    ) -> Result<TraitImpl, Error> {
        trace!("About to translate trait impl:\n{:?}", rust_id);
        trace!("Trait impl id:\n{:?}", def_id);

        let tcx = self.tcx;
        let span = item_meta.span.rust_span();
        let erase_regions = false;
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        bt_ctx.push_generics_for_def(span, rust_id, def)?;
        let generics = bt_ctx.get_generics();

        let hax::Def::Impl {
            impl_subject: hax::ImplSubject::Trait(trait_pred),
            items,
            ..
        } = def
        else {
            unreachable!()
        };
        let implemented_trait_id = &trait_pred.trait_ref.def_id;
        let implemented_trait_rust_id = implemented_trait_id.into();
        let items: Vec<(TraitItemName, &hax::AssocItem, Option<Arc<hax::Def>>)> = items
            .iter()
            .map(|item| {
                let name = TraitItemName(item.name.clone());
                // Warning: don't call `hax_def` on associated functions because this triggers
                // hax crashes on functions with higher-kinded predicates like
                // `Iterator::scan`.
                let def = if matches!(item.kind, hax::AssocKind::Type | hax::AssocKind::Const) {
                    let def = bt_ctx.t_ctx.hax_def(&item.def_id);
                    Some(def)
                } else {
                    None
                };
                (name, item, def)
            })
            .collect_vec();

        // Retrieve the information about the implemented trait.
        let trait_id = bt_ctx.register_trait_decl_id(span, implemented_trait_rust_id)?;
        // We already tested above whether the trait should be filtered
        let trait_id = trait_id.unwrap();
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
                trait_refs: Vec::new(),
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
                tcx.param_env(rust_id),
                rust_trait_ref.def_id,
                rust_trait_ref.args,
                None,
            );
            let parent_trait_refs: Vec<TraitRef> =
                bt_ctx.translate_trait_impl_exprs(span, erase_regions, &parent_trait_refs)?;
            let parent_trait_refs: Vector<TraitClauseId, TraitRef> = parent_trait_refs.into();

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
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();

        use rustc_middle::ty::AssocKind;
        for (name, item, item_def) in &items {
            let name = name.clone();
            let rust_item_id = (&item.def_id).into();
            let item_span = tcx.def_span(rust_item_id);
            match &item.kind {
                hax::AssocKind::Fn => {
                    let fun_id = bt_ctx.register_fun_decl_id(item_span, rust_item_id);
                    let AssocItemContainer::TraitImplContainer {
                        overrides_default, ..
                    } = item.container
                    else {
                        unreachable!()
                    };
                    if overrides_default {
                        provided_methods.push((name, fun_id));
                    } else {
                        required_methods.push((name, fun_id));
                    }
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
                    let hax::Def::AssocTy {
                        value: Some(ty), ..
                    } = item_def.as_deref().unwrap()
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
        for item in tcx
            .associated_items(implemented_trait_rust_id)
            .in_definition_order()
        {
            let item_span = tcx.def_span(item.def_id);
            match &item.kind {
                AssocKind::Fn => (),
                AssocKind::Const => {
                    let name = TraitItemName(item.name.to_string());
                    // Does the trait impl provide an implementation for this const?
                    let c = match partial_consts.get(&name) {
                        Some(c) => c.clone(),
                        None => {
                            // The item is not defined in the trait impl: the trait decl *must*
                            // define a default value.
                            // The parameters of the constant are the same as those of the item
                            // that declares them.
                            GlobalDeclRef {
                                id: bt_ctx.register_global_decl_id(item_span, item.def_id),
                                generics: implemented_trait.generics.clone(),
                            }
                        }
                    };
                    consts.push((name, c));
                }
                AssocKind::Type => {
                    let name = TraitItemName(item.name.to_string());
                    // Does the trait impl provide an implementation for this type?
                    let ty = match partial_types.get(&name) {
                        Some(ty) => ty.clone(),
                        None => {
                            // The item is not defined in the trait impl:
                            // the trait decl *must* define a default value.
                            // TODO: should we normalize the type?
                            let ty = tcx
                                .type_of(item.def_id)
                                .instantiate_identity()
                                .sinto(&bt_ctx.hax_state);
                            bt_ctx.translate_ty(item_span, erase_regions, &ty)?
                        }
                    };
                    types.push((name.clone(), ty));

                    // Retrieve the trait refs
                    let trait_refs = bt_ctx.translate_trait_refs_from_impl_trait_item(
                        rust_id,
                        &rust_implemented_trait_ref,
                        item,
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
