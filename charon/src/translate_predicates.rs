#![allow(dead_code)]
use crate::formatter::Formatter;
use crate::gast::*;
use crate::meta::Meta;
use crate::translate_ctx::*;
use crate::translate_types::*;
use crate::types::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters};
use rustc_hir::def_id::DefId;

/// Do we fail hard if we don't find the clause implementing a trait ref when
/// resolving trait parameters?
const PANIC_IF_NO_TRAIT_CLAUSE_FOUND: bool = true;

/// Same as [TraitClause] but enriched with information about the parent
/// predicates and the predicates which apply to the associated types.
/// We need this information to solve the provenance of traits coming from
/// where clauses.
///
/// Note that this type is recursive.
///
/// We have to do this because of this kind of situations
///```text
/// trait Foo {
///   type W: Bar // Bar contains a method bar
/// }
///
/// fn f<T : Foo>(x : T::W) {
///   x.bar(); // We need to refer to the trait clause declared for Foo::W
///            // and this clause is not immediately accessible.
/// }
///
/// trait FooChild : Foo {}
///
/// fn g<T : FooChild>(x: <T as Foo>::W) { ... }
///                       ^^^^^^^^^^^^^
/// //     We need to have access to a clause `FooChild : Foo` to solve this
/// ```
#[derive(Debug, Clone)]
pub(crate) struct FullTraitClause {
    /// Note that this is local to the
    pub clause_id: TraitClauseId::Id,
    /// [Some] if this is the top clause, [None] if this is about a parent/
    /// associated type clause.
    pub meta: Option<Meta>,
    pub trait_id: TraitDeclId::Id,
    pub generics: RGenericArgs,
    /// Parent clauses
    pub parent_clauses: Vec<FullTraitClause>,
    /// Clauses coming from the trait items (should be the types)
    pub items_clauses: Vec<(TraitItemName, Vec<FullTraitClause>)>,
}

impl FullTraitClause {
    pub(crate) fn to_trait_clause(&self) -> TraitClause {
        TraitClause {
            clause_id: self.clause_id,
            meta: self.meta.unwrap(),
            trait_id: self.trait_id,
            generics: self.generics.clone(),
        }
    }

    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: for<'a> TypeFormatter<'a, Region<RegionVarId::Id>>,
    {
        let clause = self.to_trait_clause();
        clause.fmt_with_ctx(ctx)
    }
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, EnumToGetters)]
pub(crate) enum Predicate {
    Trait(FullTraitClause),
    TypeOutlives(TypeOutlives),
    RegionOutlives(RegionOutlives),
    TraitType(RTraitTypeConstraint),
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn convert_params_info(info: hax::ParamsInfo) -> ParamsInfo {
        ParamsInfo {
            num_region_params: info.num_region_params,
            num_type_params: info.num_type_params,
            num_const_generic_params: info.num_const_generic_params,
            num_trait_clauses: info.num_trait_clauses,
            num_regions_outlive: info.num_regions_outlive,
            num_types_outlive: info.num_types_outlive,
            num_trait_type_constraints: info.num_trait_type_constraints,
        }
    }

    pub(crate) fn get_parent_params_info(&mut self, def_id: DefId) -> Option<ParamsInfo> {
        let params_info =
            hax::get_parent_params_info(&self.hax_state, def_id).map(Self::convert_params_info);

        // Very annoying: because we may filter some marker traits (like [core::marker::Sized])
        // we have to recompute the number of trait clauses!
        match params_info {
            None => None,
            Some(mut params_info) => {
                let tcx = self.t_ctx.tcx;
                let parent_id = tcx.generics_of(def_id).parent.unwrap();

                let mut num_trait_clauses = 0;
                // **IMPORTANT**: we do NOT want to use [TyCtxt::predicates_of].
                let preds = tcx.predicates_defined_on(parent_id).sinto(&self.hax_state);
                for (pred, _) in preds.predicates {
                    match &pred.value {
                        hax::PredicateKind::Clause(hax::Clause::Trait(clause)) => {
                            if self
                                .translate_trait_decl_id(
                                    clause.trait_ref.def_id.rust_def_id.unwrap(),
                                )
                                .is_some()
                            {
                                num_trait_clauses += 1;
                            }
                        }
                        _ => (),
                    }
                }
                params_info.num_trait_clauses = num_trait_clauses;
                Some(params_info)
            }
        }
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
        let predicates: hax::GenericPredicates = self
            .t_ctx
            .tcx
            .predicates_defined_on(def_id)
            .sinto(&self.hax_state);

        // We reorder the predicates to make sure that the trait clauses come
        // *before* the other clauses. This way we are sure that, when translating,
        // all the trait clauses are in the context if we need them.
        //
        // Example:
        // ```
        // f<T : Foo<S = U::S>, U : Foo>(...)
        //               ^^^^
        //        must make sure we have U : Foo in the contextx
        //                before translating this
        // ```
        let (trait_clauses, preds): (
            Vec<(hax::Predicate, hax::Span)>,
            Vec<(hax::Predicate, hax::Span)>,
        ) = predicates.predicates.into_iter().partition(|x| {
            matches!(
                &x.0.value,
                hax::PredicateKind::Clause(hax::Clause::Trait(_))
            )
        });
        let preds: Vec<(hax::Predicate, hax::Span)> =
            trait_clauses.into_iter().chain(preds.into_iter()).collect();
        hax::GenericPredicates {
            parent: predicates.parent,
            predicates: preds,
        }
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
                trace!("Predicates of parent: {:?}", preds);
                self.translate_predicates(&preds);
            }
        }

        // The predicates of the current definition
        let preds = self.get_predicates_of(def_id);
        trace!("Local predicates: {:?}", preds);
        self.translate_predicates(&preds);
    }

    pub(crate) fn translate_predicates(&mut self, preds: &hax::GenericPredicates) {
        self.translate_predicates_vec(&preds.predicates);
    }

    pub(crate) fn translate_predicates_vec(&mut self, preds: &Vec<(hax::Predicate, hax::Span)>) {
        trace!("Predicates:\n{:?}", preds);
        // We reorder the trait predicates so that we translate the predicates
        // which introduce trait clauses *before* translating the other predicates
        // (because in order to translate the latters we might need to solve
        // trait parameters which need the formers).
        use hax::{Clause, PredicateKind};
        let (preds_traits, preds): (Vec<_>, Vec<_>) = preds
            .iter()
            .partition(|(pred, _)| matches!(&pred.value, PredicateKind::Clause(Clause::Trait(_))));
        let preds = preds_traits.into_iter().chain(preds.into_iter());

        for (pred, span) in preds {
            match self.translate_predicate(pred, span) {
                None => (),
                Some(pred) => match pred {
                    Predicate::Trait(p) => self.trait_clauses.push_back(p),
                    Predicate::TypeOutlives(p) => self.types_outlive.push(p),
                    Predicate::RegionOutlives(p) => self.regions_outlive.push(p),
                    Predicate::TraitType(p) => self.trait_type_constraints.push(p),
                },
            }
        }
    }

    /// Returns an [Option] because we may filter clauses about builtin or
    /// auto traits like [core::marker::Sized] and [core::marker::Sync].
    pub(crate) fn translate_trait_clause(
        &mut self,
        trait_pred: &hax::TraitPredicate,
        span: Option<&hax::Span>,
    ) -> Option<FullTraitClause> {
        // Note sure what this is about
        assert!(trait_pred.is_positive);
        // Note sure what this is about
        assert!(!trait_pred.is_const);

        let trait_ref = &trait_pred.trait_ref;
        let trait_id = self.translate_trait_decl_id(trait_ref.def_id.rust_def_id.unwrap());
        // We might have to ignore the trait
        let trait_id = trait_id?;

        let (regions, types, const_generics) = self
            .translate_substs(None, &trait_ref.generic_args)
            .unwrap();
        // There are no trait refs
        let generics = GenericArgs::new(regions, types, const_generics, Vec::new());

        let parent_clauses = self.with_local_trait_clauses(&mut |ctx: &mut Self| {
            trait_pred
                .parent_preds
                .iter()
                .filter_map(|x| ctx.translate_trait_clause(x, None))
                .collect()
        });

        let items_clauses = trait_pred
            .items_preds
            .iter()
            .map(|(name, clauses)| {
                let clauses: Vec<_> = self.with_local_trait_clauses(&mut |ctx: &mut Self| {
                    // We need to add a self clause refering the current trait decl
                    ctx.self_trait_clause = Some((trait_id, generics.clone()));

                    // We can translate the clause
                    clauses
                        .iter()
                        .filter_map(|clause| {
                            // The clause is inside a binder
                            assert!(clause.bound_vars.is_empty());
                            ctx.translate_trait_clause(&clause.value, None)
                        })
                        .collect()
                });
                (TraitItemName(name.to_string()), clauses)
            })
            .collect();

        let clause_id = self.trait_clauses_counter.fresh_id();
        let meta = span.map(|x| self.translate_meta_from_rspan(x.clone()));
        Some(FullTraitClause {
            clause_id,
            meta,
            trait_id,
            generics,
            parent_clauses,
            items_clauses,
        })
    }

    pub(crate) fn translate_predicate(
        &mut self,
        pred: &hax::Predicate,
        span: &hax::Span,
    ) -> Option<Predicate> {
        trace!("{:?}", pred);
        // Skip the binder (which lists the quantified variables).
        // By doing so, we allow the predicates to contain DeBruijn indices,
        // but it is ok because we only do a simple check.
        let pred_kind = &pred.value;
        use hax::{Clause, PredicateKind};
        match pred_kind {
            PredicateKind::Clause(Clause::Trait(trait_pred)) => self
                .translate_trait_clause(trait_pred, Some(span))
                .map(Predicate::Trait),
            PredicateKind::Clause(Clause::RegionOutlives(p)) => {
                let r0 = self.translate_region(&p.0);
                let r1 = self.translate_region(&p.1);
                Some(Predicate::RegionOutlives(OutlivesPred(r0, r1)))
            }
            PredicateKind::Clause(Clause::TypeOutlives(p)) => {
                let ty = self.translate_ty(&p.0).unwrap();
                let r = self.translate_region(&p.1);
                Some(Predicate::TypeOutlives(OutlivesPred(ty, r)))
            }
            PredicateKind::Clause(Clause::Projection(p)) => {
                // This is used to express constraints over associated types.
                // For instance:
                // ```
                // T : Foo<S = String>
                //         ^^^^^^^^^^
                // ```
                let hax::ProjectionPredicate {
                    impl_source,
                    substs,
                    type_name,
                    ty,
                } = p;

                let trait_ref = self.translate_trait_impl_source(impl_source);
                // The trait ref should be Some(...): the marker traits (that
                // we may filter) don't have associated types.
                let trait_ref = trait_ref.unwrap();

                let (regions, types, const_generics) = self.translate_substs(None, substs).unwrap();
                let generics = GenericArgs {
                    regions,
                    types,
                    const_generics,
                    trait_refs: Vec::new(),
                };
                let ty = self.translate_ty(ty).unwrap();
                let type_name = TraitItemName(type_name.clone());
                Some(Predicate::TraitType(TraitTypeConstraint {
                    trait_ref,
                    generics,
                    type_name,
                    ty,
                }))
            }
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
            .filter_map(|x| self.translate_trait_impl_source(x))
            .collect()
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn translate_trait_impl_source<R>(
        &mut self,
        impl_source: &hax::ImplSource,
    ) -> Option<TraitRef<R>>
    where
        R: Eq + Clone,
        Self: TyTranslator<R>,
        Self: Formatter<TraitDeclId::Id> + for<'a> Formatter<&'a R>,
    {
        trace!("impl_source: {:?}", impl_source);
        use hax::ImplSourceKind;

        let trait_decl_ref = {
            let trait_ref = &impl_source.trait_ref;
            let trait_id = self.translate_trait_decl_id(trait_ref.def_id.rust_def_id.unwrap())?;
            let generics = self
                .translate_substs_and_trait_refs(None, &trait_ref.generic_args, &trait_ref.traits)
                .unwrap();
            TraitDeclRef { trait_id, generics }
        };

        let trait_ref = match &impl_source.kind {
            ImplSourceKind::UserDefined(data) => {
                let def_id = data.impl_def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_impl_id(def_id);
                // We already tested above whether the trait should be filtered
                let trait_id = trait_id.unwrap();
                let trait_id = TraitInstanceId::TraitImpl(trait_id);

                let generics = self
                    .translate_substs_and_trait_refs(None, &data.substs, &data.nested)
                    .unwrap();
                TraitRef {
                    trait_id,
                    generics,
                    trait_decl_ref,
                }
            }
            ImplSourceKind::Param(trait_ref, trait_refs, constness) => {
                assert!(trait_ref.bound_vars.is_empty());
                assert!(*constness == hax::BoundConstness::NotConst);
                let trait_ref = &trait_ref.value;

                let def_id = trait_ref.def_id.rust_def_id.unwrap();
                // Remark: we already filtered the marker traits when translating
                // the trait decl ref: the trait id should be Some(...).
                let trait_id = self.translate_trait_decl_id(def_id).unwrap();

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
                    trait_decl_ref,
                }
            }
            ImplSourceKind::Object(_) => unimplemented!(),
            ImplSourceKind::Builtin(trait_ref, traits) => {
                assert!(trait_ref.bound_vars.is_empty());
                let trait_ref = &trait_ref.value;
                let def_id = trait_ref.def_id.rust_def_id.unwrap();
                // Remark: we already filtered the marker traits when translating
                // the trait decl ref: the trait id should be Some(...).
                let trait_id = self.translate_trait_decl_id(def_id).unwrap();

                let trait_id = TraitInstanceId::BuiltinOrAuto(trait_id);
                let generics = self
                    .translate_substs_and_trait_refs(None, &trait_ref.generic_args, traits)
                    .unwrap();
                TraitRef {
                    trait_id,
                    generics,
                    trait_decl_ref,
                }
            }
            ImplSourceKind::AutoImpl(data) => {
                let def_id = data.trait_def_id.rust_def_id.unwrap();
                // Remark: we already filtered the marker traits when translating
                // the trait decl ref: the trait id should be Some(...).
                let trait_id = self.translate_trait_decl_id(def_id).unwrap();
                let trait_id = TraitInstanceId::BuiltinOrAuto(trait_id);

                TraitRef {
                    trait_id,
                    generics: GenericArgs::empty(),
                    trait_decl_ref,
                }
            }
            ImplSourceKind::TraitUpcasting(_) => unimplemented!(),
        };
        Some(trait_ref)
    }

    fn match_trait_clauses<R>(
        &self,
        trait_id: TraitDeclId::Id,
        generics: &GenericArgs<R>,
        current_group_id: &TraitInstanceId,
        current_id: &TraitInstanceId,
        clause_trait_id: TraitDeclId::Id,
        clause_generics: &RGenericArgs,
    ) -> bool
    where
        R: Eq + Clone,
        Self: TyTranslator<R>,
        Self: Formatter<TraitDeclId::Id> + for<'a> Formatter<&'a R>,
    {
        trace!("Matching trait clauses");
        // Check if the clause is about the same trait
        if clause_trait_id != trait_id {
            trace!("Not the same trait id");
            false
        } else {
            // Ignoring the regions for now
            let tgt_types = &generics.types;
            let tgt_const_generics = &generics.const_generics;

            let src_types: Vec<Ty<R>> = clause_generics
                .types
                .iter()
                .map(|x| {
                    self.convert_rty(x)
                        .replace_self_trait_instance_id(current_group_id.clone())
                })
                .collect();
            let src_const_generics = &clause_generics.const_generics;

            trace!(
                "Matching with {}:\n- target_param: {}{}\n- current clause: {}{}\n- current clause types after subst : {}",
                current_id.fmt_with_ctx(self),
                self.format_object(trait_id),
                generics.fmt_with_ctx(self),
                self.format_object(clause_trait_id),
                clause_generics.fmt_with_ctx(self),
                src_types.iter().map(|x| x.fmt_with_ctx(self)).collect::<Vec<_>>().join(", ")
            );

            // We simply check the equality between the arguments:
            // there are no universally quantified variables to unify.
            // TODO: normalize the trait clauses (we actually
            // need to check equality **modulo** equality clauses)
            // TODO: if we need to unify (later, when allowing universal
            // quantification over clause parameters), use types_utils::TySubst.
            let matched = &src_types == tgt_types && src_const_generics == tgt_const_generics;
            trace!("Match successful: {}", matched);
            matched
        }
    }

    /// Find the trait instance fullfilling a trait obligation.
    /// TODO: having to do this is very annoying. Isn't there a better way?
    fn find_trait_clause_for_param<R>(
        &self,
        trait_id: TraitDeclId::Id,
        generics: &GenericArgs<R>,
    ) -> TraitInstanceId
    where
        R: Eq + Clone,
        Self: TyTranslator<R>,
        Self: Formatter<TraitDeclId::Id> + for<'a> Formatter<&'a R>,
    {
        // Try to match with Self
        if let Some((clause_trait_id, clause_generics)) = &self.self_trait_clause &&
            self.match_trait_clauses(trait_id, generics, &TraitInstanceId::SelfId, &TraitInstanceId::SelfId, *clause_trait_id, clause_generics)
        {
            return TraitInstanceId::SelfId;
        }

        // Try to match with the local clauses
        for trait_clause in &self.trait_clauses {
            let current_id = TraitInstanceId::Clause(trait_clause.clause_id);
            let clause = self.find_trait_clause_for_param_in_clause(
                trait_id,
                generics,
                &TraitInstanceId::SelfId,
                &current_id,
                trait_clause,
            );
            if let Some(id) = clause {
                return id;
            }
        }

        // Could not find a clause
        let trait_ref = format!(
            "{}{}",
            self.format_object(trait_id),
            generics.fmt_with_ctx(self)
        );
        let clauses: Vec<String> = self
            .self_trait_clause
            .clone()
            .into_iter()
            .chain(
                self.trait_clauses
                    .clone()
                    .into_iter()
                    .map(|x| (x.trait_id, x.generics)),
            )
            .map(|(id, gens)| format!("{}{}", self.format_object(id), gens.fmt_with_ctx(self),))
            .collect();
        let clauses = clauses.join("\n");
        if PANIC_IF_NO_TRAIT_CLAUSE_FOUND {
            unreachable!(
            "Could not find a clause for parameter:\n- target param: {}\n- available clauses:\n{}",
                trait_ref, clauses
            );
        } else {
            // Return the UNKNOWN clause
            log::warn!(
                "Could not find a clause for parameter:\n- target param: {}\n- available clauses:\n{}",
                trait_ref, clauses
            );
            TraitInstanceId::Unknown(trait_ref)
        }
    }

    fn find_trait_clause_for_param_in_clause<R>(
        &self,
        trait_id: TraitDeclId::Id,
        generics: &GenericArgs<R>,
        current_group_id: &TraitInstanceId,
        current_id: &TraitInstanceId,
        trait_clause: &FullTraitClause,
    ) -> Option<TraitInstanceId>
    where
        R: Eq + Clone,
        Self: TyTranslator<R>,
        Self: Formatter<TraitDeclId::Id> + for<'a> Formatter<&'a R>,
    {
        // Match with the current clause
        if self.match_trait_clauses(
            trait_id,
            generics,
            current_group_id,
            current_id,
            trait_clause.trait_id,
            &trait_clause.generics,
        ) {
            return Some(current_id.clone());
        } else {
            // Explore the parents
            for parent_clause in &trait_clause.parent_clauses {
                let parent_id = TraitInstanceId::ParentClause(
                    Box::new(current_id.clone()),
                    trait_clause.trait_id,
                    parent_clause.clause_id,
                );

                if let Some(id) = self.find_trait_clause_for_param_in_clause(
                    trait_id,
                    generics,
                    &parent_id,
                    &parent_id,
                    parent_clause,
                ) {
                    return Some(id);
                }
            }

            // Explore the items
            for (item_name, item_clauses) in &trait_clause.items_clauses {
                for item_clause in item_clauses {
                    let item_clause_id = TraitInstanceId::ItemClause(
                        Box::new(current_id.clone()),
                        trait_clause.trait_id,
                        item_name.clone(),
                        item_clause.clause_id,
                    );

                    if let Some(id) = self.find_trait_clause_for_param_in_clause(
                        trait_id,
                        generics,
                        current_id,
                        &item_clause_id,
                        item_clause,
                    ) {
                        return Some(id);
                    }
                }
            }
        }

        // Could not find any clause
        None
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
    ) -> Option<ETraitRef> {
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
    ) -> Option<RTraitRef> {
        self.translate_trait_impl_source(impl_source)
    }
}
