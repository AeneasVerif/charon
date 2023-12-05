use crate::common::*;
use crate::formatter::IntoFormatter;
use crate::gast::*;
use crate::translate_ctx::*;
use crate::types::*;
use crate::ullbc_ast as ast;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;
use std::collections::HashMap;

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
                .subst_identity()
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
        let subst = rust_impl_trait_ref.substs;
        let bounds = tcx.item_bounds(decl_item.def_id);
        let param_env = tcx.param_env(trait_impl_def_id);
        let bounds = tcx.subst_and_normalize_erasing_regions(subst, param_env, bounds);
        let erase_regions = false;

        // Solve the predicate bounds
        let mut trait_refs = Vec::new();
        for bound in bounds {
            if let rustc_middle::ty::PredicateKind::Clause(rustc_middle::ty::Clause::Trait(
                trait_pred,
            )) = bound.kind().skip_binder()
            {
                let trait_ref = rustc_middle::ty::Binder::dummy(trait_pred.trait_ref);
                let trait_ref = hax::solve_trait(&self.hax_state, param_env, trait_ref);
                let trait_ref =
                    self.translate_trait_impl_source(span, erase_regions, &trait_ref)?;
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
    ) -> Result<(TraitItemName, (Ty, GlobalDeclId::Id)), Error> {
        let ty = self.translate_ty_from_trait_item(item)?;
        let name = TraitItemName(item.name.to_string());
        let id = self.translate_global_decl_id(item.def_id);
        Ok((name, (ty, id)))
    }

    /// Add the self trait clause, for itself (if it is a trait declaration) or
    /// for its parent (if it is a trait item).
    ///
    /// We take a def id parameter because the clause may be retrieved from
    /// an id which is not the id of the item under scrutinee (if the current
    /// id is for an item trait, we need to lookup the trait itself and give
    /// its id).
    pub(crate) fn add_self_trait_clause(&mut self, def_id: DefId) -> Result<(), Error> {
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
        let (pred, span) = predicates.predicates.iter().next_back().unwrap();
        let pred = pred.sinto(&self.hax_state);
        let span = span.sinto(&self.hax_state);

        // Convert to a clause
        assert!(pred.bound_vars.is_empty());
        let self_pred =
            if let hax::PredicateKind::Clause(hax::Clause::Trait(trait_pred)) = pred.value {
                if self
                    .translate_trait_decl_id(trait_pred.trait_ref.def_id.rust_def_id.unwrap())
                    .is_some()
                {
                    trait_pred
                } else {
                    panic!();
                }
            } else {
                panic!();
            };

        // Convert
        let mut initialized = false;
        let self_instance_id_gen = Box::new(move || {
            assert!(!initialized);
            initialized = true;
            TraitInstanceId::SelfId
        });
        let self_clause = self.with_local_trait_clauses(self_instance_id_gen, move |s| {
            s.translate_trait_clause(&span, &self_pred)
        })?;
        trace!(
            "self clause: {}",
            self_clause.unwrap().fmt_with_ctx(&self.into_fmt())
        );
        Ok(())
    }

    /// Similar to [add_self_trait_clause] but for trait implementations.
    ///
    /// We call this when translating trait impls and trait impl items.
    pub(crate) fn add_trait_impl_self_trait_clause(
        &mut self,
        impl_id: TraitImplId::Id,
    ) -> Result<(), Error> {
        let def_id = *self.t_ctx.trait_impl_id_to_def_id.get(&impl_id).unwrap();
        trace!("id: {:?}", def_id);

        // Retrieve the trait ref representing "self"
        let tcx = self.t_ctx.tcx;
        let rustc_middle::ty::ImplSubject::Trait(trait_ref) =
            tcx.impl_subject(def_id).subst_identity() else { unreachable!() };

        // Wrap it in a [TraitPredicate] so that when calling [sinto] we retrieve
        // the parent and item predicates.
        let trait_pred = rustc_middle::ty::TraitPredicate {
            trait_ref,
            // Not really necessary (dummy value)
            constness: rustc_middle::ty::BoundConstness::NotConst,
            // Not really necessary
            polarity: rustc_middle::ty::ImplPolarity::Positive,
        };
        let trait_pred = trait_pred.sinto(&self.hax_state);

        // Save the self clause (and its parent/item clauses)
        let mut initialized = false;
        let span = tcx.def_span(def_id).sinto(&self.t_ctx.hax_state);
        let _ = self.with_local_trait_clauses(
            Box::new(move || {
                assert!(!initialized);
                initialized = true;
                TraitInstanceId::SelfId
            }),
            move |s| s.translate_trait_clause(&span, &trait_pred),
        )?;
        Ok(())
    }

    pub(crate) fn with_parent_trait_clauses<T>(
        &mut self,
        clause_id: TraitInstanceId,
        trait_decl_id: TraitDeclId::Id,
        f: &mut dyn FnMut(&mut Self) -> T,
    ) -> T {
        let mut parent_clause_id_gen = TraitClauseId::Generator::new();
        let parent_trait_instance_id_gen = Box::new(move || {
            let fresh_id = parent_clause_id_gen.fresh_id();
            TraitInstanceId::ParentClause(Box::new(clause_id.clone()), trait_decl_id, fresh_id)
        });

        self.with_local_trait_clauses(parent_trait_instance_id_gen, f)
    }

    pub(crate) fn with_item_trait_clauses<T>(
        &mut self,
        clause_id: TraitInstanceId,
        trait_decl_id: TraitDeclId::Id,
        item_name: String,
        f: &mut dyn FnMut(&mut Self) -> T,
    ) -> T {
        let mut item_clause_id_gen = TraitClauseId::Generator::new();
        let item_clause_id_gen = Box::new(move || {
            let fresh_id = item_clause_id_gen.fresh_id();
            TraitInstanceId::ItemClause(
                Box::new(clause_id.clone()),
                trait_decl_id,
                TraitItemName(item_name.clone()),
                fresh_id,
            )
        });

        self.with_local_trait_clauses(item_clause_id_gen, f)
    }
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// Remark: this **doesn't** register the def id (on purpose)
    pub(crate) fn translate_trait_item_name(&mut self, rust_id: DefId) -> TraitItemName {
        // Translate the name
        let name = self.item_def_id_to_name(rust_id);
        let (name, id) = name.name.last().unwrap().as_ident();
        assert!(id.is_zero());
        TraitItemName(name.to_string())
    }

    pub(crate) fn translate_trait_decl(&mut self, rust_id: DefId) {
        // TODO: for now, if there is an error while translating the parameters/
        // predicates of the declaration, we ignore it altogether, while we should
        // save somewhere that we failed to extract it.
        if self.translate_trait_decl_aux(rust_id).is_err() {
            let span = self.tcx.def_span(rust_id);
            self.span_err(
                span,
                &format!(
                    "Ignoring the following trait decl due to an error: {:?}",
                    rust_id
                ),
            );
            // TODO
        }
    }

    /// Auxliary helper to properly handle errors, see [translate_trait_decl].
    fn translate_trait_decl_aux(&mut self, rust_id: DefId) -> Result<(), Error> {
        trace!("About to translate trait decl:\n{:?}", rust_id);

        let def_id = self.translate_trait_decl_id(rust_id);
        // We may need to ignore the trait (happens if the trait is a marker
        // trait like [core::marker::Sized]
        if def_id.is_none() {
            return Ok(());
        }
        let def_id = def_id.unwrap();

        trace!("Trait decl id:\n{:?}", def_id);

        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        let name = bt_ctx
            .t_ctx
            .extended_def_id_to_name(&rust_id.sinto(&bt_ctx.hax_state));

        // Translate the generic
        bt_ctx.translate_generic_params(rust_id)?;

        // Add the trait clauses
        bt_ctx.while_registering_trait_clauses(move |bt_ctx| {
            // Add the self trait clause
            bt_ctx.add_self_trait_clause(rust_id)?;

            // Translate the predicates.
            bt_ctx.with_parent_trait_clauses(TraitInstanceId::SelfId, def_id, &mut |s| {
                s.translate_predicates_of(None, rust_id)
            })
        })?;

        // TODO: move this below (we don't need to perform this function call exactly here)
        let preds = bt_ctx.get_predicates();

        // Explore the associated items
        // We do something subtle here: TODO: explain
        let tcx = bt_ctx.t_ctx.tcx;
        let mut consts = Vec::new();
        let mut types = Vec::new();
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();
        for item in tcx.associated_items(rust_id).in_definition_order() {
            use rustc_middle::ty::AssocKind;

            let has_default_value = item.defaultness(tcx).has_value();
            match &item.kind {
                AssocKind::Fn => {
                    let method_name = bt_ctx.t_ctx.translate_trait_item_name(item.def_id);
                    // Skip the provided methods for the *external* trait declarations,
                    // but still remember their name.
                    if has_default_value {
                        // This is a *provided* method
                        if rust_id.is_local() {
                            let fun_id = bt_ctx.translate_fun_decl_id(item.def_id);
                            provided_methods.push((method_name, Some(fun_id)));
                        } else {
                            provided_methods.push((method_name, None));
                        }
                    } else {
                        // This is a required method (no default implementation)
                        let fun_id = bt_ctx.translate_fun_decl_id(item.def_id);
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
                        (name, (ty, Some(id)))
                    } else {
                        let ty = bt_ctx.translate_ty_from_trait_item(item)?;
                        let name = TraitItemName(item.name.to_string());
                        (name, (ty, None))
                    };
                    consts.push(c);
                }
                AssocKind::Type => {
                    let name = item.name.to_string();

                    // Translating the predicates
                    {
                        // TODO: this is an ugly manip
                        let bounds = tcx.item_bounds(item.def_id).subst_identity();
                        use crate::rustc_middle::query::Key;
                        let span = bounds.default_span(tcx);
                        let bounds: Vec<_> = bounds.into_iter().map(|x| (x, span)).collect();
                        let bounds = bounds.sinto(&bt_ctx.hax_state);

                        // Register the trait clauses as item trait clauses
                        bt_ctx.with_item_trait_clauses(
                            TraitInstanceId::SelfId,
                            def_id,
                            name.clone(),
                            &mut |s| s.translate_predicates_vec(&bounds),
                        )?;
                    }

                    // Retrieve the trait clauses which are specific to this item
                    // - we simply need to filter the trait clauses by using their id.
                    let item_trait_clauses: Vec<_> = bt_ctx
                        .trait_clauses
                        .values()
                        .filter_map(|c| {
                            c.to_trait_clause_with_id(&|id| match id {
                                TraitInstanceId::ItemClause(
                                    box TraitInstanceId::SelfId,
                                    _,
                                    TraitItemName(item_name),
                                    clause_id,
                                ) => {
                                    if item_name == &name {
                                        Some(*clause_id)
                                    } else {
                                        None
                                    }
                                }
                                _ => None,
                            })
                        })
                        .collect();

                    let ty = if has_default_value {
                        Some(bt_ctx.translate_ty_from_trait_item(item)?)
                    } else {
                        None
                    };

                    types.push((TraitItemName(name), (item_trait_clauses, ty)));
                }
            }
        }

        // Note that in the generics returned by [get_generics], the trait refs
        // only contain the local trait clauses.
        let generics = bt_ctx.get_generics();
        // TODO: maybe we should do something about the predicates?

        let parent_clauses = bt_ctx.get_parent_trait_clauses();

        // Debugging:
        {
            let ctx = bt_ctx.into_fmt();
            let clauses = bt_ctx
                .trait_clauses
                .values()
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

        // In case of a trait implementation, some values may not have been
        // provided, in case the declaration provided default values. We
        // check those, and lookup the relevant values.
        let trait_decl = ast::TraitDecl {
            def_id,
            is_local: rust_id.is_local(),
            name,
            meta: self.translate_meta_from_rid(rust_id),
            generics,
            preds,
            parent_clauses,
            consts,
            types,
            required_methods,
            provided_methods,
        };
        self.trait_decls.insert(def_id, trait_decl);

        Ok(())
    }

    pub(crate) fn translate_trait_impl(&mut self, rust_id: DefId) {
        // TODO: for now, if there is an error while translating the parameters/
        // predicates of the declaration, we ignore it altogether, while we should
        // save somewhere that we failed to extract it.
        if self.translate_trait_impl_aux(rust_id).is_err() {
            let span = self.tcx.def_span(rust_id);
            self.span_err(
                span,
                &format!(
                    "Ignoring the following trait impl due to an error: {:?}",
                    rust_id
                ),
            );
            // TODO
        }
    }

    /// Auxliary helper to properly handle errors, see [translate_impl_decl].
    fn translate_trait_impl_aux(&mut self, rust_id: DefId) -> Result<(), Error> {
        trace!("About to translate trait impl:\n{:?}", rust_id);

        let def_id = self.translate_trait_impl_id(rust_id);
        // We may need to ignore the trait
        if def_id.is_none() {
            return Ok(());
        }
        let def_id = def_id.unwrap();
        trace!("Trait impl id:\n{:?}", def_id);

        let tcx = self.tcx;
        let span = tcx.def_span(rust_id);
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        let name = bt_ctx
            .t_ctx
            .extended_def_id_to_name(&rust_id.sinto(&bt_ctx.hax_state));
        let erase_regions = false;

        // Translate the generics
        bt_ctx.translate_generic_params(rust_id)?;

        // Add the trait self clauses
        bt_ctx.while_registering_trait_clauses(move |bt_ctx| {
            // Translate the predicates
            bt_ctx.translate_predicates_of(None, rust_id)?;

            // Add the self trait clause
            bt_ctx.add_trait_impl_self_trait_clause(def_id)?;

            //
            bt_ctx.solve_trait_obligations_in_trait_clauses(span);

            Ok(())
        })?;

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
            let trait_id = bt_ctx.translate_trait_decl_id(trait_rust_id);
            // We already tested above whether the trait should be filtered
            let trait_id = trait_id.unwrap();

            let rustc_middle::ty::ImplSubject::Trait(rust_trait_ref) =
                    tcx.impl_subject(rust_id).subst_identity() else { unreachable!() };
            let trait_ref = rust_trait_ref.sinto(&bt_ctx.hax_state);
            let (regions, types, const_generics) =
                bt_ctx.translate_substs(span, erase_regions, None, &trait_ref.generic_args)?;

            let parent_trait_refs = hax::solve_item_traits(
                &bt_ctx.hax_state,
                tcx.param_env(rust_id),
                rust_trait_ref.def_id,
                rust_trait_ref.substs,
                None,
            );
            let parent_trait_refs: Vec<TraitRef> =
                bt_ctx.translate_trait_impl_sources(span, erase_regions, &parent_trait_refs)?;
            let parent_trait_refs: TraitClauseId::Vector<TraitRef> =
                TraitClauseId::Vector::from(parent_trait_refs);

            let generics = GenericArgs {
                regions,
                types,
                const_generics,
                trait_refs: Vec::new(),
            };
            let trait_ref = TraitDeclRef { trait_id, generics };
            (trait_rust_id, trait_ref, rust_trait_ref, parent_trait_refs)
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

        // Explore the trait decl method items to retrieve the list of required methods
        use std::collections::HashSet;
        let mut decl_required_methods: HashSet<String> = HashSet::new();
        for item in tcx
            .associated_items(implemented_trait_rust_id)
            .in_definition_order()
        {
            if let AssocKind::Fn = &item.kind && !item.defaultness(tcx).has_value() {
                decl_required_methods.insert(item.name.to_string());
            }
        }

        // Explore the clauses of the

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
                    let method_name = bt_ctx.t_ctx.translate_trait_item_name(item.def_id);
                    let fun_id = bt_ctx.translate_fun_decl_id(item.def_id);

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
                    let (name, c) = bt_ctx.translate_const_from_trait_item(item)?;
                    consts.insert(name, c);
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
        let mut types: Vec<(TraitItemName, (Vec<TraitRef>, Ty))> = Vec::new();
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
                            // The item is not defined in the trait impl:
                            // the trait decl *must* define a default value.
                            bt_ctx.translate_const_from_trait_item(item)?.1
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

                    types.push((name, (trait_refs, ty)));
                }
            }
        }

        let trait_impl = ast::TraitImpl {
            def_id,
            is_local: rust_id.is_local(),
            name,
            meta: bt_ctx.t_ctx.translate_meta_from_rid(rust_id),
            impl_trait: implemented_trait,
            generics: bt_ctx.get_generics(),
            preds: bt_ctx.get_predicates(),
            parent_trait_refs,
            consts,
            types,
            required_methods,
            provided_methods,
        };
        self.trait_impls.insert(def_id, trait_impl);

        Ok(())
    }
}
