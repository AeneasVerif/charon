#![allow(dead_code)]
use crate::common::Result;
use crate::gast::{ParamsInfo, TraitRef};
use crate::translate_ctx::{BodyTransCtx, TransCtx};
use crate::translate_types;
use crate::types::{ConstGeneric, RTy, Region, RegionVarId, TraitClause};
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    pub(crate) fn get_params_info(&mut self, def_id: DefId) -> ParamsInfo {
        let tcx = self.tcx;

        // Compute the number of generics
        let mut num_region_params = 0;
        let mut num_type_params = 0;
        let mut num_const_generic_params = 0;

        let generics = tcx.generics_of(def_id);
        use rustc_middle::ty::GenericParamDefKind;
        for param in &generics.params {
            match param.kind {
                GenericParamDefKind::Lifetime => num_region_params += 1,
                GenericParamDefKind::Type { .. } => num_type_params += 1,
                GenericParamDefKind::Const { .. } => num_const_generic_params += 1,
            }
        }

        ParamsInfo {
            num_region_params,
            num_type_params,
            num_const_generic_params,
        }
    }

    pub(crate) fn get_parent_params_info(&mut self, def_id: DefId) -> Option<ParamsInfo> {
        self.tcx
            .generics_of(def_id)
            .parent
            .map(|parent_id| self.get_params_info(parent_id))
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    // TODO: there are too many variants of this, we should merge them
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
        // TODO: use predicates_defined_on?
        let preds = tcx.predicates_of(def_id).sinto(&self.t_ctx.hax_state);

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

        use crate::gast::TraitOrClauseId;

        match impl_source {
            ImplSource::UserDefined(data) => {
                let def_id = data.impl_def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_id(def_id);
                let trait_id = TraitOrClauseId::Trait(trait_id);

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
                // TODO: trait id: doesn't work
                let trait_id = self.translate_trait_id(def_id);
                let trait_id = TraitOrClauseId::Trait(trait_id); // TODO: this doesn't work

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
            ImplSource::Object(_) => unimplemented!(),
            ImplSource::Builtin(trait_ref, traits) => {
                assert!(trait_ref.bound_vars.is_empty());
                let trait_ref = &trait_ref.value;
                let def_id = trait_ref.def_id.rust_def_id.unwrap();
                // TODO: trait id: doesn't work
                let trait_id = self.translate_trait_id(def_id);
                let trait_id = TraitOrClauseId::Trait(trait_id); // TODO: this doesn't work

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
