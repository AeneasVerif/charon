#![allow(dead_code)]
use crate::common::Result;
use crate::gast;
use crate::gast::{ParamsInfo, TraitRef};
use crate::translate_ctx::{BodyTransCtx, TransCtx};
use crate::translate_types;
use crate::types::{ConstGeneric, ETy, RTy, Region, RegionVarId, TraitClause, TraitClauseId};
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
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
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    // TODO: there are too many variants of this function, we should merge them
    pub(crate) fn translate_substs_with_regions(
        &mut self,
        substs: &Vec<hax::GenericArg>,
    ) -> Result<(Vec<Region<RegionVarId::Id>>, Vec<RTy>, Vec<ConstGeneric>)> {
        let region_vars_map = &self.region_vars_map.clone();
        let bound_vars = &self.bound_vars.clone();
        let region_translator =
            &|r: &_| translate_types::translate_non_erased_region(region_vars_map, bound_vars, r);

        let mut regions = vec![];
        let mut params = vec![];
        let mut cgs = vec![];
        for param in substs {
            match param {
                hax::GenericArg::Type(param_ty) => {
                    let param_ty = self.translate_ty(region_translator, param_ty)?;
                    params.push(param_ty);
                }
                hax::GenericArg::Lifetime(region) => {
                    regions.push(region_translator(region));
                }
                hax::GenericArg::Const(c) => {
                    cgs.push(self.translate_constant_expr_to_const_generic(c));
                }
            }
        }

        Result::Ok((regions, params, cgs))
    }

    /// This function should be called **after** we translated the generics
    /// (type parameters, regions...).
    pub(crate) fn translate_predicates_of(&mut self, def_id: DefId) {
        let tcx = self.t_ctx.tcx;

        // Get the predicates
        // Note that we need to know *all* the predicates: we start
        // with the parent.
        // TODO: use predicates_defined_on?
        match tcx.generics_of(def_id).parent {
            None => (),
            Some(parent_id) => {
                let preds = tcx.predicates_of(parent_id).sinto(&self.t_ctx.hax_state);
                self.translate_predicates(preds);
            }
        }

        // The predicates of the current definition
        let preds = tcx.predicates_of(def_id).sinto(&self.t_ctx.hax_state);
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
                    let (region_params, type_params, const_generic_params) = self
                        .translate_substs_with_regions(&trait_ref.generic_args)
                        .unwrap();

                    let meta = self.translate_meta_from_rspan(span);
                    let clause_id = self.trait_clauses_counter.fresh_id();
                    self.trait_clauses.push_back(TraitClause {
                        clause_id,
                        meta,
                        trait_id,
                        region_params,
                        type_params,
                        const_generic_params,
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

    pub(crate) fn translate_trait_impl_source(
        &mut self,
        impl_source: &hax::ImplSource,
    ) -> TraitRef {
        use hax::ImplSource;

        use crate::gast::TraitInstanceId;

        match impl_source {
            ImplSource::UserDefined(data) => {
                let def_id = data.impl_def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_id(def_id);
                let trait_id = TraitInstanceId::Trait(trait_id);

                let (region_args, type_args, const_generic_args) = self
                    .translate_subst_generic_args_in_body(None, &data.substs)
                    .unwrap();
                let traits = data
                    .nested
                    .iter()
                    .map(|x| self.translate_trait_impl_source(x))
                    .collect();
                TraitRef {
                    trait_id,
                    region_args,
                    type_args,
                    const_generic_args,
                    traits,
                }
            }
            ImplSource::Param(trait_ref, traits, constness) => {
                assert!(trait_ref.bound_vars.is_empty());
                assert!(*constness == hax::BoundConstness::NotConst);
                let trait_ref = &trait_ref.value;

                let def_id = trait_ref.def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_id(def_id);

                // Retrieve the arguments
                let (region_args, type_args, const_generic_args) = self
                    .translate_subst_generic_args_in_body(None, &trait_ref.generic_args)
                    .unwrap();
                let traits: Vec<TraitRef> = traits
                    .iter()
                    .map(|x| self.translate_trait_impl_source(x))
                    .collect();

                // We need to find the trait clause which corresponds to
                // this obligation.
                let clause_id = {
                    let mut clause_id: Option<TraitClauseId::Id> = None;

                    let tgt_type_args = type_args;
                    let tgt_const_generic_args = const_generic_args;

                    for trait_clause in &self.trait_clauses {
                        // Check if the clause is about the same trait
                        if trait_clause.trait_id != trait_id {
                            continue;
                        }

                        let src_type_args: Vec<ETy> = trait_clause
                            .type_params
                            .iter()
                            .map(|x| x.erase_regions())
                            .collect();
                        let src_const_generic_args = &trait_clause.const_generic_params;

                        // We simply check the equality between the arguments:
                        // there are no universally quantified variables to unify.
                        // TODO: normalize the trait clauses (we actually
                        // need to check equality **modulo** equality clauses)
                        // TODO: if we need to unify (later, when allowing universal
                        // quantification over clause parameters), use types_utils::TySubst.
                        if src_type_args == tgt_type_args
                            && src_const_generic_args == &tgt_const_generic_args
                        {
                            clause_id = Some(trait_clause.clause_id);
                            break;
                        }
                    }
                    // We should have found a clause
                    match clause_id {
                        Some(id) => id,
                        None => {
                            use crate::formatter::Formatter;
                            let trait_ref = format!(
                                "{}{}",
                                self.format_object(trait_id),
                                gast::fmt_args_no_traits(
                                    self,
                                    &region_args,
                                    &tgt_type_args,
                                    &tgt_const_generic_args
                                )
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

                assert!(traits.is_empty());
                // Ignore the arguments: we forbid using universal quantifiers
                // on the trait clauses for now.
                TraitRef {
                    trait_id,
                    region_args: Vec::new(),
                    type_args: Vec::new(),
                    const_generic_args: Vec::new(),
                    traits,
                }
            }
            ImplSource::Object(_) => unimplemented!(),
            ImplSource::Builtin(trait_ref, traits) => {
                assert!(traits.is_empty());

                assert!(trait_ref.bound_vars.is_empty());
                let trait_ref = &trait_ref.value;
                let def_id = trait_ref.def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_id(def_id);
                let trait_id = TraitInstanceId::Builtin(trait_id);
                let (region_args, type_args, const_generic_args) = self
                    .translate_subst_generic_args_in_body(None, &trait_ref.generic_args)
                    .unwrap();
                let traits = traits
                    .iter()
                    .map(|x| self.translate_trait_impl_source(x))
                    .collect();

                TraitRef {
                    trait_id,
                    region_args,
                    type_args,
                    const_generic_args,
                    traits,
                }
            }
            ImplSource::TraitUpcasting(_) => unimplemented!(),
        }
    }
}
