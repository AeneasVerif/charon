#![allow(dead_code)]
use crate::formatter::Formatter;
use crate::gast::ParamsInfo;
use crate::translate_ctx::BodyTransCtx;
use crate::translate_types::TyTranslator;
use crate::types::{
    ConstGeneric, ETraitRef, GenericArgs, RTraitRef, TraitClause, TraitDeclId, TraitInstanceId,
    TraitRef, Ty, TypeVarId,
};
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn convert_params_info(info: hax::ParamsInfo) -> ParamsInfo {
        ParamsInfo {
            num_region_params: info.num_region_params,
            num_type_params: info.num_type_params,
            num_const_generic_params: info.num_const_generic_params,
            num_trait_clauses: info.num_trait_clauses,
        }
    }

    pub(crate) fn get_params_info(&mut self, def_id: DefId) -> ParamsInfo {
        Self::convert_params_info(hax::get_params_info(&self.hax_state, def_id))
    }

    pub(crate) fn get_parent_params_info(&mut self, def_id: DefId) -> Option<ParamsInfo> {
        hax::get_parent_params_info(&self.hax_state, def_id).map(Self::convert_params_info)
    }

    pub(crate) fn get_predicates_of(&mut self, def_id: DefId) -> hax::GenericPredicates {
        // **IMPORTANT**:
        // There are two functions which allow to retrieve the predicates of
        // a definition:
        // - [TyCtxt::predicates_of]
        // - [TyCtxt::predicates_defined_on]
        // If we use [TyCtxt::predicates_of] on a trait `Foo`, we get an
        // additional predicate `Self : Foo` (i.e., the trait requires itself),
        // which is not what we want.
        self.t_ctx
            .tcx
            .predicates_defined_on(def_id)
            .sinto(&self.hax_state)
    }

    /// This function should be called **after** we translated the generics
    /// (type parameters, regions...).
    pub(crate) fn translate_predicates_of(&mut self, def_id: DefId) {
        trace!("def_id: {:?}", def_id);
        let tcx = self.t_ctx.tcx;

        // Get the predicates
        // Note that we need to know *all* the predicates: we start
        // with the parent.
        match tcx.generics_of(def_id).parent {
            None => (),
            Some(parent_id) => {
                let preds = self.get_predicates_of(parent_id);
                self.translate_predicates(preds);
            }
        }

        // The predicates of the current definition
        let preds = self.get_predicates_of(def_id);
        self.translate_predicates(preds);
    }

    pub(crate) fn translate_predicates(&mut self, preds: hax::GenericPredicates) {
        self.translate_predicates_vec(preds.predicates);
    }

    pub(crate) fn translate_predicates_vec(&mut self, preds: Vec<(hax::Predicate, hax::Span)>) {
        for (pred, span) in preds {
            match self.translate_predicate(pred, span) {
                None => (),
                Some(trait_clause) => self.trait_clauses.push_back(trait_clause),
            }
        }
    }

    pub(crate) fn translate_predicate(
        &mut self,
        pred: hax::Predicate,
        span: hax::Span,
    ) -> Option<TraitClause> {
        // Skip the binder (which lists the quantified variables).
        // By doing so, we allow the predicates to contain DeBruijn indices,
        // but it is ok because we only do a simple check.
        let pred_kind = &pred.value;
        use hax::{Clause, PredicateKind};
        match pred_kind {
            PredicateKind::Clause(Clause::Trait(trait_pred)) => {
                // Note sure what this is about
                assert!(trait_pred.is_positive);
                // Note sure what this is about
                assert!(!trait_pred.is_const);

                let trait_ref = &trait_pred.trait_ref;
                let trait_id = self.translate_trait_decl_id(trait_ref.def_id.rust_def_id.unwrap());
                let (regions, types, const_generics) = self
                    .translate_substs(None, &trait_ref.generic_args)
                    .unwrap();
                // There are no trait refs
                let generics = GenericArgs::new(regions, types, const_generics, Vec::new());

                let meta = self.translate_meta_from_rspan(span);
                let clause_id = self.trait_clauses_counter.fresh_id();
                Some(TraitClause {
                    clause_id,
                    meta,
                    trait_id,
                    generics,
                })
            }
            PredicateKind::Clause(Clause::RegionOutlives(_)) => unimplemented!(),
            PredicateKind::Clause(Clause::TypeOutlives(_)) => unimplemented!(),
            PredicateKind::Clause(Clause::Projection(_)) => unimplemented!(),
            PredicateKind::Clause(Clause::ConstArgHasType(..)) => {
                // I don't really understand that one. Why don't they put
                // the type information in the const generic parameters
                // directly? For now we just ignore it.
                None
            }
            PredicateKind::WellFormed(_) => unimplemented!(),
            PredicateKind::ObjectSafe(_) => unimplemented!(),
            PredicateKind::ClosureKind(_, _, _) => unimplemented!(),
            PredicateKind::Subtype(_) => unimplemented!(),
            PredicateKind::Coerce(_) => unimplemented!(),
            PredicateKind::ConstEvaluatable(_) => unimplemented!(),
            PredicateKind::ConstEquate(_, _) => unimplemented!(),
            PredicateKind::TypeWellFormedFromEnv(_) => unimplemented!(),
            PredicateKind::Ambiguous => unimplemented!(),
            PredicateKind::AliasRelate(..) => unimplemented!(),
        }
    }

    pub(crate) fn translate_trait_impl_sources<R>(
        &mut self,
        impl_sources: &Vec<hax::ImplSource>,
    ) -> Vec<TraitRef<R>>
    where
        R: Eq + Clone,
        Self: TyTranslator<R>,
        Self: Formatter<TraitDeclId::Id> + for<'a> Formatter<&'a R>,
    {
        impl_sources
            .iter()
            .map(|x| self.translate_trait_impl_source(x))
            .collect()
    }

    pub(crate) fn translate_trait_impl_source<R>(
        &mut self,
        impl_source: &hax::ImplSource,
    ) -> TraitRef<R>
    where
        R: Eq + Clone,
        Self: TyTranslator<R>,
        Self: Formatter<TraitDeclId::Id> + for<'a> Formatter<&'a R>,
    {
        trace!("impl_source: {:?}", impl_source);
        use hax::ImplSource;

        match impl_source {
            ImplSource::UserDefined(data) => {
                let def_id = data.impl_def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_impl_id(def_id);
                let trait_id = TraitInstanceId::Trait(trait_id);

                let generics = self
                    .translate_substs_and_trait_refs(None, &data.substs, &data.nested)
                    .unwrap();
                TraitRef { trait_id, generics }
            }
            ImplSource::Param(trait_ref, trait_refs, constness) => {
                assert!(trait_ref.bound_vars.is_empty());
                assert!(*constness == hax::BoundConstness::NotConst);
                let trait_ref = &trait_ref.value;

                let def_id = trait_ref.def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_decl_id(def_id);

                // Retrieve the arguments
                let generics = self
                    .translate_substs_and_trait_refs(None, &trait_ref.generic_args, trait_refs)
                    .unwrap();
                assert!(generics.trait_refs.is_empty());

                // We need to find the trait clause which corresponds to
                // this obligation.
                let trait_id = self.find_trait_clause_for_param(trait_id, &generics);

                assert!(generics.trait_refs.is_empty());
                // Ignore the arguments: we forbid using universal quantifiers
                // on the trait clauses for now.
                TraitRef {
                    trait_id,
                    generics: GenericArgs::empty(),
                }
            }
            ImplSource::Object(_) => unimplemented!(),
            ImplSource::Builtin(trait_ref, traits) => {
                assert!(traits.is_empty());

                assert!(trait_ref.bound_vars.is_empty());
                let trait_ref = &trait_ref.value;
                let def_id = trait_ref.def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_decl_id(def_id);
                let trait_id = TraitInstanceId::BuiltinOrAuto(trait_id);
                let generics = self
                    .translate_substs_and_trait_refs(None, &trait_ref.generic_args, traits)
                    .unwrap();
                TraitRef { trait_id, generics }
            }
            ImplSource::AutoImpl(data) => {
                let def_id = data.trait_def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_decl_id(def_id);
                let trait_id = TraitInstanceId::BuiltinOrAuto(trait_id);

                TraitRef {
                    trait_id,
                    generics: GenericArgs::empty(),
                }
            }
            ImplSource::TraitUpcasting(_) => unimplemented!(),
        }
    }

    /// Find the trait instance fullfilling a trait obligation.
    /// TODO: having to do this is very annoying. Isn't there a better way?
    fn find_trait_clause_for_param<R>(
        &mut self,
        trait_id: TraitDeclId::Id,
        generics: &GenericArgs<R>,
    ) -> TraitInstanceId
    where
        R: Eq + Clone,
        Self: TyTranslator<R>,
        Self: Formatter<TraitDeclId::Id> + for<'a> Formatter<&'a R>,
    {
        let tgt_types = &generics.types;
        let tgt_const_generics = &generics.const_generics;

        let match_trait_clauses = &|trait_clause: &TraitClause| {
            // Check if the clause is about the same trait
            if trait_clause.trait_id != trait_id {
                false
            } else {
                let src_types: Vec<Ty<R>> = trait_clause
                    .generics
                    .types
                    .iter()
                    .map(|x| self.convert_rty(x))
                    .collect();
                let src_const_generics = &trait_clause.generics.const_generics;

                // We simply check the equality between the arguments:
                // there are no universally quantified variables to unify.
                // TODO: normalize the trait clauses (we actually
                // need to check equality **modulo** equality clauses)
                // TODO: if we need to unify (later, when allowing universal
                // quantification over clause parameters), use types_utils::TySubst.
                &src_types == tgt_types && src_const_generics == tgt_const_generics
            }
        };

        // Try to match the self trait clause
        if let Some(self_clause) = &self.self_trait_clause && match_trait_clauses(self_clause) {
            return TraitInstanceId::SelfId;
        }

        // Otherwise match the parameter clauses
        for trait_clause in &self.trait_clauses {
            // Match with the clause
            if match_trait_clauses(trait_clause) {
                return TraitInstanceId::Clause(trait_clause.clause_id);
            }

            // Very annoying, but we have to do the following because of this
            // kind of situations:
            // ```
            // trait Foo {
            //   type W: Bar // Bar contains a method bar
            // }
            //
            // fn f<T : Foo>(x : T::W) {
            //   x.bar(); // We need to refer to the trait clause declared for Foo::W
            // }
            // ```
            //
            // Match with the trait clauses of the associated types present
            // in the trait.
            // With the example above: we may have (unsuccessfully) matched
            // with the clause `T : Foo`, now we dive inside `Foo` and look
            // at its associated types.

            // **IMPORTANT**: we attempt to lookup the trait declaration.
            // If we succeed, we match. Otherwise, we skip.
            // Note that we translate traits before functions (and before
            // trait methods), and in most situations we should need to
            // dive into trait declarations to find clauses to match with
            // for methods, so it should be ok.
            // We could also force the translation of the trait we want
            // to lookup at this point, but I'm afraid of loops.
            if let Some(trait_decl) = self.t_ctx.trait_decls.get(trait_clause.trait_id) {
                trace!(
                    "Looked up trait declaration: {}",
                    trait_decl.name.to_string()
                );

                // Create the substitutions - TODO: very heavy...
                // TODO: dealing with the regions is a mess...
                // We check there are none for now.
                assert!(trait_decl.generics.regions.is_empty());
                let ty_subst = crate::types_utils::make_type_subst(
                    trait_decl.generics.types.iter().map(|x| x.index),
                    trait_clause.generics.types.iter(),
                );
                use std::iter::FromIterator;
                let ty_subst: std::collections::HashMap<TypeVarId::Id, Ty<R>> =
                    std::collections::HashMap::from_iter(
                        ty_subst.into_iter().map(|(k, v)| (k, self.convert_rty(&v))),
                    );

                let cg_subst = crate::types_utils::make_cg_subst(
                    trait_decl.generics.const_generics.iter().map(|x| x.index),
                    trait_clause.generics.const_generics.iter(),
                );

                // Explore the associated types
                for (name, (clauses, _)) in &trait_decl.types {
                    for clause in clauses {
                        trace!("Matching with: {name}");
                        trace!(
                            "Trait id: {:?}, Clause trait id: {:?}",
                            trait_id,
                            clause.trait_id
                        );
                        trace!("Clause: {:?}", clause);

                        if clause.trait_id != trait_id {
                            trace!("Not the same trait id");
                            continue;
                        }
                        trace!("Same trait id");

                        // TODO: dealing with the regions is a mess...
                        // Checking there are none for now
                        assert!(clause.generics.regions.is_empty());

                        // Substitute
                        let src_types: Vec<Ty<R>> = clause
                            .generics
                            .types
                            .iter()
                            .map(|x| {
                                self.convert_rty(x)
                                    .substitute(
                                        &|r| r.clone(),
                                        &|tid| ty_subst.get(tid).unwrap().clone(),
                                        &|cgid| cg_subst.get(cgid).unwrap().clone(),
                                    )
                                    .replace_self_trait_instance_id(TraitInstanceId::Clause(
                                        clause.clause_id,
                                    ))
                            })
                            .collect();

                        let src_const_generics: Vec<ConstGeneric> = clause
                            .generics
                            .const_generics
                            .iter()
                            .map(|x| x.substitute(&|cgid| cg_subst.get(cgid).unwrap().clone()))
                            .collect();

                        trace!(
                            "- tgt_types: {}\n- tgt_const_generics: {}\n- src_types: {}\n- src_const_generics: {}",
                            tgt_types
                                .iter()
                                .map(|x| x.fmt_with_ctx(self))
                                .collect::<Vec<_>>()
                                .join(", "),
                            tgt_const_generics
                                .iter()
                                .map(|x| x.fmt_with_ctx(self))
                                .collect::<Vec<_>>()
                                .join(", "),
                            src_types
                                .iter()
                                .map(|x| x.fmt_with_ctx(self))
                                .collect::<Vec<_>>()
                                .join(", "),
                            src_const_generics
                                .iter()
                                .map(|x| x.fmt_with_ctx(self))
                                .collect::<Vec<_>>()
                                .join(", ")
                        );

                        // See [match_trait_clauses]
                        if &src_types == tgt_types && &src_const_generics == tgt_const_generics {
                            return TraitInstanceId::TraitTypeClause(
                                Box::new(TraitInstanceId::Clause(trait_clause.clause_id)),
                                name.clone(),
                                clause.clause_id,
                            );
                        }
                    }
                }
            }
        }

        // We couldn't find a clause
        let trait_ref = format!(
            "{}{}",
            self.format_object(trait_id),
            generics.fmt_with_ctx(self)
        );
        let clauses: Vec<String> = self
            .self_trait_clause
            .iter()
            .chain(self.trait_clauses.iter())
            .map(|x| x.fmt_with_ctx(self))
            .collect();
        let clauses = clauses.join("\n");
        unreachable!(
            "Could not find a clause for parameter:\n- target param: {}\n- available clauses:\n{}",
            trait_ref, clauses
        );
    }

    pub(crate) fn translate_trait_impl_sources_erased_regions(
        &mut self,
        impl_sources: &Vec<hax::ImplSource>,
    ) -> Vec<ETraitRef> {
        self.translate_trait_impl_sources(impl_sources)
    }

    pub(crate) fn translate_trait_impl_source_erased_regions(
        &mut self,
        impl_source: &hax::ImplSource,
    ) -> ETraitRef {
        self.translate_trait_impl_source(impl_source)
    }

    pub(crate) fn translate_trait_impl_sources_with_regions(
        &mut self,
        impl_sources: &Vec<hax::ImplSource>,
    ) -> Vec<RTraitRef> {
        self.translate_trait_impl_sources(impl_sources)
    }

    pub(crate) fn translate_trait_impl_source_with_regions(
        &mut self,
        impl_source: &hax::ImplSource,
    ) -> RTraitRef {
        self.translate_trait_impl_source(impl_source)
    }
}
