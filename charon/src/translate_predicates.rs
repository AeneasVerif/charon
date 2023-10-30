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

/// Same as [TraitClause], but where the clause id is a [TraitInstanceId].
/// We need this information to solve the provenance of traits coming from
/// where clauses: when translating the where clauses and adding them to the
/// context, we recursively explore their parent/item clauses.
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
pub(crate) struct NonLocalTraitClause {
    pub clause_id: TraitInstanceId,
    /// [Some] if this is the top clause, [None] if this is about a parent/
    /// associated type clause.
    pub meta: Option<Meta>,
    pub trait_id: TraitDeclId::Id,
    pub generics: RGenericArgs,
}

impl NonLocalTraitClause {
    pub(crate) fn to_trait_clause(&self) -> Option<TraitClause> {
        if let TraitInstanceId::Clause(id) = &self.clause_id {
            Some(TraitClause {
                clause_id: *id,
                meta: self.meta,
                trait_id: self.trait_id,
                generics: self.generics.clone(),
            })
        } else {
            None
        }
    }

    pub(crate) fn to_trait_clause_with_id(
        &self,
        get_id: &dyn Fn(&TraitInstanceId) -> Option<TraitClauseId::Id>,
    ) -> Option<TraitClause> {
        match get_id(&self.clause_id) {
            None => None,
            Some(clause_id) => Some(TraitClause {
                clause_id,
                meta: self.meta,
                trait_id: self.trait_id,
                generics: self.generics.clone(),
            }),
        }
    }

    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: for<'a> TypeFormatter<'a, Region<RegionVarId::Id>>
            + for<'a> TypeFormatter<'a, ErasedRegion>,
    {
        let clause_id = self.clause_id.fmt_with_ctx(ctx);
        let trait_id = ctx.format_object(self.trait_id);
        let generics = self.generics.fmt_with_ctx(ctx);
        format!("[{clause_id}]: {trait_id}{generics}")
    }
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, EnumToGetters)]
pub(crate) enum Predicate {
    Trait(NonLocalTraitClause),
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
        let tcx = self.t_ctx.tcx;
        let param_env = tcx.param_env(def_id);
        // Remark: we don't convert the predicates yet because we need to
        // normalize them before.
        let predicates = tcx.predicates_defined_on(def_id);
        let parent: Option<hax::DefId> = predicates.parent.sinto(&self.hax_state);
        let predicates: Vec<_> = predicates.predicates.iter().collect();
        trace!("Predicates of {:?}:\n{:?}", def_id, predicates);

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
        let (trait_clauses, non_trait_preds): (
            Vec<&(rustc_middle::ty::Predicate<'_>, rustc_span::Span)>,
            Vec<&(rustc_middle::ty::Predicate<'_>, rustc_span::Span)>,
        ) = predicates.into_iter().partition(|x| {
            matches!(
                &x.0.kind().skip_binder(),
                rustc_middle::ty::PredicateKind::Clause(rustc_middle::ty::Clause::Trait(_))
            )
        });

        let trait_clauses: Vec<(rustc_middle::ty::TraitPredicate<'_>, rustc_span::Span)> =
            trait_clauses
                .into_iter()
                .map(|(pred, span)| {
                    if let rustc_middle::ty::PredicateKind::Clause(
                        rustc_middle::ty::Clause::Trait(tr),
                    ) = &pred.kind().no_bound_vars().unwrap()
                    {
                        // Normalize the trait clause
                        let tr = tcx.normalize_erasing_regions(param_env, *tr);
                        (tr, *span)
                    } else {
                        unreachable!();
                    }
                })
                .collect();

        let trait_preds: Vec<_> = trait_clauses
            .iter()
            .map(|(tr, span)| {
                let value =
                    hax::PredicateKind::Clause(hax::Clause::Trait(tr.sinto(&self.hax_state)));
                let pred = hax::Binder {
                    value,
                    bound_vars: Vec::new(),
                };
                (pred, span.sinto(&self.hax_state))
            })
            .collect();

        let non_trait_preds: Vec<_> = non_trait_preds
            .iter()
            .map(|(pred, span)| (pred.sinto(&self.hax_state), span.sinto(&self.hax_state)))
            .collect();

        let predicates: Vec<(hax::Predicate, hax::Span)> = trait_preds
            .into_iter()
            .chain(non_trait_preds.into_iter())
            .collect();
        hax::GenericPredicates { parent, predicates }
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
            None => {
                trace!("No parents for {:?}", def_id);
            }
            Some(parent_id) => {
                let preds = self.get_predicates_of(parent_id);
                trace!("Predicates of parent ({:?}): {:?}", parent_id, preds);
                self.translate_predicates(&preds);
            }
        }

        let clauses = self
            .trait_clauses
            .values()
            .map(|c| c.fmt_with_ctx(self))
            .collect::<Vec<String>>()
            .join(",\n");
        trace!(
            "Local trait clauses of {:?} after translating the predicates of the parent:\n{}",
            def_id,
            clauses
        );

        // The predicates of the current definition
        let preds = self.get_predicates_of(def_id);
        trace!("Local predicates of {:?}:\n{:?}", def_id, preds);
        self.translate_predicates(&preds);

        let clauses = self
            .trait_clauses
            .values()
            .map(|c| c.fmt_with_ctx(self))
            .collect::<Vec<String>>()
            .join(",\n");
        trace!(
            "All trait clauses of {:?} (parents + locals):\n{}",
            def_id,
            clauses
        );
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
        let preds: Vec<_> = preds_traits.into_iter().chain(preds.into_iter()).collect();

        for (pred, span) in preds {
            match self.translate_predicate(pred, span) {
                None => (),
                Some(pred) => match pred {
                    Predicate::Trait(_) => {
                        // Don't need to do anything because the clause is already
                        // registered in [self.trait_clauses]
                    }
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
    ) -> Option<NonLocalTraitClause> {
        // Note sure what this is about
        assert!(trait_pred.is_positive);

        let trait_ref = &trait_pred.trait_ref;
        let trait_id = self.translate_trait_decl_id(trait_ref.def_id.rust_def_id.unwrap());
        // We might have to ignore the trait
        let trait_id = trait_id?;

        let (regions, types, const_generics) = self
            .translate_substs(None, &trait_ref.generic_args)
            .unwrap();
        // There are no trait refs
        let generics = GenericArgs::new(regions, types, const_generics, Vec::new());

        // Compute the current clause id
        let clause_id = (self.trait_instance_id_gen)();
        let meta = span.map(|x| self.translate_meta_from_rspan(x.clone()));

        // Immediately register the clause (we may need to refer to it in the parent/
        // item clauses)
        let trait_clause = NonLocalTraitClause {
            clause_id: clause_id.clone(),
            meta,
            trait_id,
            generics,
        };
        self.trait_clauses
            .insert(trait_clause.clause_id.clone(), trait_clause.clone());

        let mut parent_clause_id_gen = TraitClauseId::Generator::new();
        let nclause_id = clause_id.clone();
        let parent_trait_instance_id_gen = Box::new(move || {
            let fresh_id = parent_clause_id_gen.fresh_id();
            TraitInstanceId::ParentClause(Box::new(nclause_id.clone()), trait_id, fresh_id)
        });
        // [translate_trait_clause] takes care of registering the clause
        let _parent_clauses: Vec<_> =
            self.with_local_trait_clauses(parent_trait_instance_id_gen, &mut |ctx: &mut Self| {
                trait_pred
                    .parent_preds
                    .iter()
                    .filter_map(|x| ctx.translate_trait_clause(x, None))
                    .collect()
            });

        // [translate_trait_clause] takes care of registering the clause
        let _items_clauses: Vec<_> = trait_pred
            .items_preds
            .iter()
            .map(|(name, clauses)| {
                let mut item_clause_id_gen = TraitClauseId::Generator::new();
                let nclause_id = clause_id.clone();
                let nname = name.clone();
                let item_trait_instance_id_gen = Box::new(move || {
                    let fresh_id = item_clause_id_gen.fresh_id();
                    TraitInstanceId::ItemClause(
                        Box::new(nclause_id.clone()),
                        trait_id,
                        TraitItemName(nname.clone()),
                        fresh_id,
                    )
                });

                let clauses: Vec<_> = self.with_local_trait_clauses(
                    item_trait_instance_id_gen,
                    &mut |ctx: &mut Self| {
                        clauses
                            .iter()
                            .filter_map(|clause| {
                                // The clause is inside a binder
                                assert!(clause.bound_vars.is_empty());
                                ctx.translate_trait_clause(&clause.value, None)
                            })
                            .collect()
                    },
                );
                (TraitItemName(name.to_string()), clauses)
            })
            .collect();

        // Return
        Some(trait_clause)
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
                // Explanations about constness: https://stackoverflow.com/questions/70441495/what-is-impl-const-in-rust
                trace!(
                    "impl_source: param:\n- trait_ref: {:?}\n- trait_refs: {:?}\n- constness: {:?}",
                    trait_ref,
                    trait_refs,
                    constness
                );
                assert!(trait_ref.bound_vars.is_empty());
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
            ImplSourceKind::FnPointer(data) => {
                let ty = self.translate_ety(&data.fn_ty).unwrap();
                let trait_id = TraitInstanceId::FnPointer(Box::new(ty));
                let trait_refs = self.translate_trait_impl_sources(&data.nested);
                let generics = GenericArgs {
                    regions: vec![],
                    types: vec![],
                    const_generics: vec![],
                    trait_refs,
                };
                TraitRef {
                    trait_id,
                    generics,
                    trait_decl_ref,
                }
            }
            ImplSourceKind::TraitUpcasting(_) => unimplemented!(),
            ImplSourceKind::Error(msg) => {
                if PANIC_IF_NO_TRAIT_CLAUSE_FOUND {
                    panic!("Error during trait resolution: {}", msg)
                } else {
                    let trait_id = TraitInstanceId::Unknown(msg.clone());
                    TraitRef {
                        trait_id,
                        generics: GenericArgs::empty(),
                        trait_decl_ref,
                    }
                }
            }
        };
        Some(trait_ref)
    }

    fn match_trait_clauses<R>(
        &self,
        trait_id: TraitDeclId::Id,
        generics: &GenericArgs<R>,
        clause: &NonLocalTraitClause,
    ) -> bool
    where
        R: Eq + Clone,
        Self: TyTranslator<R>,
        Self: Formatter<TraitDeclId::Id> + for<'a> Formatter<&'a R>,
    {
        trace!("Matching trait clauses:\n- trait_id: {:?}\n- generics: {:?}\n- clause.trait_id: {:?}\n- clause.generics: {:?}",
               self.format_object(trait_id), generics.fmt_with_ctx(self),
               self.format_object(clause.trait_id), clause.generics.fmt_with_ctx(self)
        );
        // Check if the clause is about the same trait
        if clause.trait_id != trait_id {
            trace!("Not the same trait id");
            false
        } else {
            // Ignoring the regions for now
            let tgt_types = &generics.types;
            let tgt_const_generics = &generics.const_generics;

            let src_types: Vec<Ty<R>> = clause
                .generics
                .types
                .iter()
                .map(|x| self.convert_rty(x))
                .collect();
            let src_const_generics = &clause.generics.const_generics;

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
        trace!("Inside context of: {:?}", self.def_id);

        // Simply explore the trait clauses
        for trait_clause in self.trait_clauses.values() {
            if self.match_trait_clauses(trait_id, generics, trait_clause) {
                return trait_clause.clause_id.clone();
            }
        }

        // Could not find a clause
        let trait_ref = format!(
            "{}{}",
            self.format_object(trait_id),
            generics.fmt_with_ctx(self)
        );
        let clauses: Vec<String> = self
            .trait_clauses
            .values()
            .map(|x| x.fmt_with_ctx(self))
            .collect();
        if PANIC_IF_NO_TRAIT_CLAUSE_FOUND {
            let clauses = clauses.join("\n");
            unreachable!(
                "Could not find a clause for parameter:\n- target param: {}\n- available clauses:\n{}\n- context: {:?}",
                trait_ref, clauses, self.def_id
            );
        } else {
            // Return the UNKNOWN clause
            log::warn!(
                "Could not find a clause for parameter:\n- target param: {}\n- available clauses:\n{}\n- context: {:?}",
                trait_ref, clauses.join("\n"), self.def_id
            );
            TraitInstanceId::Unknown(format!(
                "Could not find a clause for parameter: {} (available clauses: {}) (context: {:?})",
                trait_ref,
                clauses.join("; "),
                self.def_id
            ))
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
