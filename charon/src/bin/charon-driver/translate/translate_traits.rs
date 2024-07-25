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
use rustc_hir::def_id::DefId;
use std::collections::HashMap;

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
    fn translate_ty_from_trait_item(
        &mut self,
        item: &rustc_middle::ty::AssocItem,
    ) -> Result<Ty, Error> {
        let erase_regions = false;
        let tcx = self.t_ctx.tcx;
        self.translate_ty(
            tcx.def_span(item.def_id),
            erase_regions,
            &tcx.type_of(item.def_id)
                .instantiate_identity()
                .sinto(&self.hax_state),
        )
    }

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

    fn translate_const_from_trait_item(
        &mut self,
        item: &rustc_middle::ty::AssocItem,
    ) -> Result<(TraitItemName, (Ty, GlobalDeclId)), Error> {
        let ty = self.translate_ty_from_trait_item(item)?;
        let name = TraitItemName(item.name.to_string());
        let span = self.t_ctx.tcx.def_span(self.def_id);
        let id = self.register_global_decl_id(span, item.def_id);
        Ok((name, (ty, id)))
    }

    /// Add the self trait clause, for itself (if it is a trait declaration) or
    /// for its parent (if it is a trait item).
    ///
    /// We take a def id parameter because the clause may be retrieved from
    /// an id which is not the id of the item under scrutinee (if the current
    /// id is for an item trait, we need to lookup the trait itself and give
    /// its id).
    pub(crate) fn translate_trait_decl_self_trait_clause(
        &mut self,
        def_id: DefId,
    ) -> Result<(), Error> {
        trace!("id: {:?}", def_id);
        // The self trait clause is actually the *last* trait predicate given by
        // [TyCtxt::predicates_of].
        // **ATTENTION**: this doesn't return the same thing as [TyCtxt::predicates_defined_on],
        // which we use elsewhere.

        // Sanity check: we should add the self trait clause before we start
        // translating the clauses.
        assert!(self.trait_clauses.is_empty());

        let predicates = self.t_ctx.tcx.predicates_of(def_id);
        trace!("predicates: {:?}", predicates);

        // Get the last predicate
        let (clause, rspan) = predicates.predicates.iter().next_back().unwrap();
        let clause: hax::Clause = clause.sinto(&self.hax_state);
        let span = rspan.sinto(&self.hax_state);

        // Convert to a clause
        assert!(clause.kind.bound_vars.is_empty());
        let hax::ClauseKind::Trait(self_pred) = clause.kind.value else {
            panic!()
        };
        assert!(self
            .register_trait_decl_id(*rspan, DefId::from(&self_pred.trait_ref.def_id))?
            .is_some());

        // Convert
        self.translate_self_trait_clause(&span, &self_pred)?;
        Ok(())
    }

    /// Similar to [add_self_trait_clause] but for trait implementations.
    ///
    /// We call this when translating trait impls and trait impl items.
    pub(crate) fn translate_trait_impl_self_trait_clause(
        &mut self,
        def_id: DefId,
    ) -> Result<(), Error> {
        trace!("id: {:?}", def_id);

        // Retrieve the trait ref representing "self"
        let tcx = self.t_ctx.tcx;
        let rustc_middle::ty::ImplSubject::Trait(trait_ref) =
            tcx.impl_subject(def_id).instantiate_identity()
        else {
            unreachable!()
        };

        // Wrap it in a [TraitPredicate] so that when calling [sinto] we retrieve
        // the parent and item predicates.
        let trait_pred = rustc_middle::ty::TraitPredicate {
            trait_ref,
            // Not really necessary
            polarity: rustc_middle::ty::PredicatePolarity::Positive,
        };
        let trait_pred = trait_pred.sinto(&self.hax_state);

        let span = tcx.def_span(def_id).sinto(&self.t_ctx.hax_state);
        // Save the self clause (and its parent/item clauses)
        self.translate_self_trait_clause(&span, &trait_pred)?;
        Ok(())
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
        use rustc_middle::ty::AssocKind;
        trace!("About to translate trait decl:\n{:?}", rust_id);
        trace!("Trait decl id:\n{:?}", def_id);

        let span = item_meta.span.rust_span();
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);
        let tcx = bt_ctx.t_ctx.tcx;
        let name = bt_ctx.t_ctx.def_id_to_name(rust_id)?;

        let hax::Def::Trait {
            generics,
            predicates,
            ..
        } = def
        else {
            panic!("Unexpected definition: {def:?}")
        };

        // Translate the generics
        bt_ctx.push_generic_params(span, generics)?;

        // Add the self trait clause
        bt_ctx.translate_trait_decl_self_trait_clause(rust_id)?;

        // Translate the rest of the predicates.
        bt_ctx.translate_predicates(
            &predicates,
            PredicateOrigin::WhereClauseOnTrait,
            &PredicateLocation::Parent(def_id),
        )?;

        // Gather the associated type clauses
        let mut type_clauses = Vec::new();
        for item in tcx.associated_items(rust_id).in_definition_order() {
            match &item.kind {
                AssocKind::Type => {
                    let item_name = TraitItemName(item.name.to_string());
                    // TODO: this is an ugly manip
                    let bounds = tcx.item_bounds(item.def_id).instantiate_identity();
                    use crate::rustc_middle::query::Key;
                    let span = bounds.default_span(tcx);
                    let bounds: Vec<_> = bounds
                        .into_iter()
                        .map(|x| (x.as_predicate(), span))
                        .collect();
                    let bounds = bounds.sinto(&bt_ctx.hax_state);
                    let origin = PredicateOrigin::TraitItem(item_name.clone());

                    // Register the trait clauses as item trait clauses
                    bt_ctx.translate_predicates_vec(
                        &bounds,
                        origin,
                        &PredicateLocation::Item(def_id, item_name.clone()),
                    )?;
                }
                AssocKind::Fn => {}
                AssocKind::Const => {}
            }
        }

        // Push the collected clauses in definition order.
        for item in tcx.associated_items(rust_id).in_definition_order() {
            match &item.kind {
                AssocKind::Type => {
                    let item_name = TraitItemName(item.name.to_string());
                    if let Some(clauses) = bt_ctx.item_trait_clauses.get(&item_name) {
                        type_clauses.push((item_name, clauses.clone()));
                    }
                }
                AssocKind::Fn => {}
                AssocKind::Const => {}
            }
        }

        // Note that in the generics returned by [get_generics], the trait refs
        // only contain the local trait clauses.
        let generics = bt_ctx.get_generics();
        // TODO: maybe we should do something about the predicates?

        // Translate the associated items
        // We do something subtle here: TODO: explain
        let mut consts = Vec::new();
        let mut const_defaults = HashMap::new();
        let mut types = Vec::new();
        let mut type_defaults = HashMap::new();
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();
        for item in tcx.associated_items(rust_id).in_definition_order() {
            let has_default_value = item.defaultness(tcx).has_value();
            match &item.kind {
                AssocKind::Fn => {
                    let span = tcx.def_span(item.def_id);
                    let method_name = bt_ctx.t_ctx.translate_trait_item_name(item.def_id)?;
                    // Skip the provided methods for the *external* trait declarations,
                    // but still remember their name (unless `extract_opaque_bodies` is set).
                    if has_default_value {
                        // This is a *provided* method
                        if rust_id.is_local() || bt_ctx.t_ctx.options.extract_opaque_bodies {
                            let fun_id = bt_ctx.register_fun_decl_id(span, item.def_id);
                            provided_methods.push((method_name, Some(fun_id)));
                        } else {
                            provided_methods.push((method_name, None));
                        }
                    } else {
                        // This is a required method (no default implementation)
                        let fun_id = bt_ctx.register_fun_decl_id(span, item.def_id);
                        required_methods.push((method_name, fun_id));
                    }
                }
                AssocKind::Const => {
                    // Check if the constant has a value (i.e., a body).
                    // We are handling a trait *declaration* so we need to
                    // check whether the constant has a default value.
                    trace!("id: {:?}\n- item: {:?}", rust_id, item);
                    let c = if has_default_value {
                        let (name, (ty, id)) = bt_ctx.translate_const_from_trait_item(item)?;
                        // The parameters of the constant are the same as those of the item that
                        // declares them.
                        let gref = GlobalDeclRef {
                            id,
                            generics: generics.identity_args(),
                        };
                        const_defaults.insert(name.clone(), gref);
                        (name, ty)
                    } else {
                        let ty = bt_ctx.translate_ty_from_trait_item(item)?;
                        let name = TraitItemName(item.name.to_string());
                        (name, ty)
                    };
                    consts.push(c);
                }
                AssocKind::Type => {
                    let item_name = TraitItemName(item.name.to_string());
                    if has_default_value {
                        let ty = bt_ctx.translate_ty_from_trait_item(item)?;
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

        let hax::Def::Impl {
            of_trait: true,
            generics,
            predicates,
        } = def
        else {
            panic!("Unexpected definition: {def:?}")
        };

        bt_ctx.push_generic_params(span, generics)?;
        bt_ctx.translate_predicates(
            &predicates,
            PredicateOrigin::WhereClauseOnImpl,
            &PredicateLocation::Base,
        )?;

        // Add the self trait clause
        bt_ctx.translate_trait_impl_self_trait_clause(rust_id)?;

        // Retrieve the information about the implemented trait.
        let (
            implemented_trait_rust_id,
            implemented_trait,
            rust_implemented_trait_ref,
            // [parent_trait_refs]: the trait refs which implement the parent
            // clauses of the implemented trait decl.
            parent_trait_refs,
        ) = {
            // TODO: what is below duplicates a bit [add_trait_impl_self_trait_clause]
            let trait_rust_id = tcx.trait_id_of_impl(rust_id).unwrap();
            let trait_id = bt_ctx.register_trait_decl_id(span, trait_rust_id)?;
            // We already tested above whether the trait should be filtered
            let trait_id = trait_id.unwrap();

            let rustc_middle::ty::ImplSubject::Trait(rust_trait_ref) =
                tcx.impl_subject(rust_id).instantiate_identity()
            else {
                unreachable!()
            };
            let trait_ref = rust_trait_ref.sinto(&bt_ctx.hax_state);
            let (regions, types, const_generics) =
                bt_ctx.translate_substs(span, erase_regions, None, &trait_ref.generic_args)?;

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

            let generics = GenericArgs {
                regions,
                types,
                const_generics,
                trait_refs: Vec::new(),
            };
            let trait_ref = TraitDeclRef { trait_id, generics };
            (trait_rust_id, trait_ref, rust_trait_ref, parent_trait_refs)
        };

        let generics = bt_ctx.get_generics();

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

        // Explore the trait decl method items to retrieve the list of required methods
        use std::collections::HashSet;
        let mut decl_required_methods: HashSet<String> = HashSet::new();
        for item in tcx
            .associated_items(implemented_trait_rust_id)
            .in_definition_order()
        {
            if let AssocKind::Fn = &item.kind
                && !item.defaultness(tcx).has_value()
            {
                decl_required_methods.insert(item.name.to_string());
            }
        }

        // Explore the associated items
        // We do something subtle here: TODO
        let tcx = bt_ctx.t_ctx.tcx;
        let mut consts = HashMap::new();
        let mut types: HashMap<TraitItemName, Ty> = HashMap::new();
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();

        use rustc_middle::ty::AssocKind;
        for item in tcx.associated_items(rust_id).in_definition_order() {
            match &item.kind {
                AssocKind::Fn => {
                    let method_name = bt_ctx.t_ctx.translate_trait_item_name(item.def_id)?;
                    let fun_id = bt_ctx.register_fun_decl_id(span, item.def_id);

                    // Check if we implement a required method or reimplement
                    // a provided method
                    let is_required = decl_required_methods.contains(&method_name.0);
                    if is_required {
                        required_methods.push((method_name, fun_id));
                    } else {
                        provided_methods.push((method_name, fun_id));
                    }
                }
                AssocKind::Const => {
                    let (name, (_ty, id)) = bt_ctx.translate_const_from_trait_item(item)?;

                    // The parameters of the constant are the same as those of the item that
                    // declares them.
                    let gref = GlobalDeclRef {
                        id,
                        generics: generics.identity_args(),
                    };
                    consts.insert(name, gref);
                }
                AssocKind::Type => {
                    let name = TraitItemName(item.name.to_string());
                    let ty = bt_ctx.translate_ty_from_trait_item(item)?;
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
                            let id = bt_ctx.translate_const_from_trait_item(item)?.1 .1;
                            // The parameters of the constant are the same as those of the item
                            // that declares them.
                            GlobalDeclRef {
                                id,
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
                            bt_ctx.translate_ty_from_trait_item(item)?
                        }
                    };

                    // Retrieve the trait refs
                    let trait_refs = bt_ctx.translate_trait_refs_from_impl_trait_item(
                        rust_id,
                        &rust_implemented_trait_ref,
                        item,
                    )?;

                    types.push((name.clone(), ty));
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
