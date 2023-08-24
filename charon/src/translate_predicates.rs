#![allow(dead_code)]
use crate::formatter::Formatter;
use crate::gast::ParamsInfo;
use crate::translate_ctx::BodyTransCtx;
use crate::translate_types::TyTranslator;
use crate::types::{ETraitRef, GenericArgs, RTraitRef, TraitRef};
use crate::types::{TraitClause, TraitClauseId, TraitDeclId, Ty};
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

    /// This function should be called **after** we translated the generics
    /// (type parameters, regions...).
    pub(crate) fn translate_predicates_of(&mut self, def_id: DefId) {
        trace!("def_id: {:?}", def_id);
        let tcx = self.t_ctx.tcx;

        // Get the predicates
        // Note that we need to know *all* the predicates: we start
        // with the parent.
        // TODO: use predicates_defined_on?
        match tcx.generics_of(def_id).parent {
            None => (),
            Some(parent_id) => {
                let preds = tcx.predicates_of(parent_id).sinto(&self.hax_state);
                self.translate_predicates(preds);
            }
        }

        // The predicates of the current definition
        let preds = tcx.predicates_of(def_id).sinto(&self.hax_state);
        self.translate_predicates(preds);
    }

    fn translate_predicates(&mut self, preds: hax::GenericPredicates) {
        for (pred, span) in preds.predicates {
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
                    let trait_id = self.translate_trait_id(trait_ref.def_id.rust_def_id.unwrap());
                    let (regions, types, const_generics) = self
                        .translate_substs(None, &trait_ref.generic_args)
                        .unwrap();
                    // There are no trait refs
                    let generics = GenericArgs::new(regions, types, const_generics, Vec::new());

                    let meta = self.translate_meta_from_rspan(span);
                    let clause_id = self.trait_clauses_counter.fresh_id();
                    self.trait_clauses.push_back(TraitClause {
                        clause_id,
                        meta,
                        trait_id,
                        generics,
                    });
                }
                PredicateKind::Clause(Clause::RegionOutlives(_)) => unimplemented!(),
                PredicateKind::Clause(Clause::TypeOutlives(_)) => unimplemented!(),
                PredicateKind::Clause(Clause::Projection(_)) => unimplemented!(),
                PredicateKind::Clause(Clause::ConstArgHasType(..)) => {
                    // I don't really understand that one. Why don't they put
                    // the type information in the const generic parameters
                    // directly? For now we just ignore it.
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
        use crate::gast::TraitInstanceId;
        use hax::ImplSource;

        match impl_source {
            ImplSource::UserDefined(data) => {
                let def_id = data.impl_def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_id(def_id);
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
                let trait_id = self.translate_trait_id(def_id);

                // Retrieve the arguments
                let generics = self
                    .translate_substs_and_trait_refs(None, &trait_ref.generic_args, trait_refs)
                    .unwrap();
                assert!(generics.trait_refs.is_empty());

                // We need to find the trait clause which corresponds to
                // this obligation.
                let clause_id = {
                    let mut clause_id: Option<TraitClauseId::Id> = None;

                    let tgt_types = &generics.types;
                    let tgt_const_generics = &generics.const_generics;

                    for trait_clause in &self.trait_clauses {
                        // Check if the clause is about the same trait
                        if trait_clause.trait_id != trait_id {
                            continue;
                        }

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
                        if &src_types == tgt_types && src_const_generics == tgt_const_generics {
                            clause_id = Some(trait_clause.clause_id);
                            break;
                        }
                    }
                    // We should have found a clause
                    match clause_id {
                        Some(id) => id,
                        None => {
                            let trait_ref = format!(
                                "{}{}",
                                self.format_object(trait_id),
                                generics.fmt_with_ctx(self)
                            );
                            let clauses: Vec<String> = self
                                .trait_clauses
                                .iter()
                                .map(|x| x.fmt_with_ctx(self))
                                .collect();
                            let clauses = clauses.join("\n");
                            unreachable!(
                                "Could not find a clause for parameter:\n- target param: {}\n- available clauses:\n{}",
                                trait_ref, clauses
                            );
                        }
                    }
                };

                let trait_id = TraitInstanceId::Clause(clause_id);

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
                let trait_id = self.translate_trait_id(def_id);
                let trait_id = TraitInstanceId::BuiltinOrAuto(trait_id);
                let generics = self
                    .translate_substs_and_trait_refs(None, &trait_ref.generic_args, traits)
                    .unwrap();
                TraitRef { trait_id, generics }
            }
            ImplSource::AutoImpl(data) => {
                let def_id = data.trait_def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_id(def_id);
                let trait_id = TraitInstanceId::BuiltinOrAuto(trait_id);

                TraitRef {
                    trait_id,
                    generics: GenericArgs::empty(),
                }
            }
            ImplSource::TraitUpcasting(_) => unimplemented!(),
        }
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
