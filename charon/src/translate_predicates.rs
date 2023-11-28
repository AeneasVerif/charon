#![allow(dead_code)]
use crate::common::*;
use crate::formatter::Formatter;
use crate::gast::*;
use crate::meta::Meta;
use crate::translate_ctx::*;
use crate::types::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters};
use rustc_hir::def_id::DefId;

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
    pub generics: GenericArgs,
}

impl NonLocalTraitClause {
    pub(crate) fn to_local_trait_clause(&self) -> Option<TraitClause> {
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
        C: TypeFormatter,
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
    TraitType(TraitTypeConstraint),
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
        // - [TyCtxt::predicates_defined_on]: returns exactly the list of predicates
        //   that the user has written on the definition:
        // - [TyCtxt::predicates_of]: returns the user defined predicates and also:
        //   - if called on a trait `Foo`, we get an additional trait clause
        //     `Self : Foo` (i.e., the trait requires itself), which is not what we want.
        //   - for the type definitions, it also returns additional type/region outlives
        //     information, which the user doesn't have to write by hand (but it doesn't
        //     add those for functions). For instance, below:
        //     ```
        //     type MutMut<'a, 'b> {
        //       x : &'a mut &'b mut u32,
        //     }
        //     ```
        //     The rust compiler adds the predicate: `'b : 'a` ('b outlives 'a).
        // For this reason we:
        // - retrieve the trait predicates with [TyCtxt::predicates_defined_on]
        // - retrieve the other predicates with [TyCtxt::predicates_of]
        //
        // Also, we reorder the predicates to make sure that the trait clauses come
        // *before* the other clauses. This way we are sure that, when translating,
        // all the trait clauses are in the context if we need them.
        //
        // Example:
        // ```
        // f<T : Foo<S = U::S>, U : Foo>(...)
        //               ^^^^
        //        must make sure we have U : Foo in the context
        //                before translating this
        // ```
        let tcx = self.t_ctx.tcx;
        let param_env = tcx.param_env(def_id);
        let parent: Option<hax::DefId>;

        let trait_preds = {
            // Remark: we don't convert the predicates yet because we need to
            // normalize them before.
            let predicates = tcx.predicates_defined_on(def_id);
            parent = predicates.parent.sinto(&self.hax_state);
            let predicates: Vec<_> = predicates.predicates.iter().collect();
            trace!(
                "TyCtxt::predicates_defined_on({:?}):\n{:?}",
                def_id,
                predicates
            );

            let trait_clauses: Vec<&(rustc_middle::ty::Predicate<'_>, rustc_span::Span)> =
                predicates
                    .into_iter()
                    .filter(|x| {
                        matches!(
                            &x.0.kind().skip_binder(),
                            rustc_middle::ty::PredicateKind::Clause(
                                rustc_middle::ty::Clause::Trait(_)
                            )
                        )
                    })
                    .collect();

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
            trait_preds
        };

        let non_trait_preds = {
            let predicates = tcx.predicates_of(def_id);
            let predicates: Vec<_> = predicates.predicates.iter().collect();
            trace!("TyCtxt::predicates_of({:?}):\n{:?}", def_id, predicates);

            let non_trait_preds: Vec<&(rustc_middle::ty::Predicate<'_>, rustc_span::Span)> =
                predicates
                    .into_iter()
                    .filter(|x| {
                        !(matches!(
                            &x.0.kind().skip_binder(),
                            rustc_middle::ty::PredicateKind::Clause(
                                rustc_middle::ty::Clause::Trait(_)
                            )
                        ))
                    })
                    .collect();
            trace!(
                "TyCtxt::predicates_of({:?}) after filtering trait clauses:\n{:?}",
                def_id,
                non_trait_preds
            );
            let non_trait_preds: Vec<_> = non_trait_preds
                .iter()
                .map(|(pred, span)| (pred.sinto(&self.hax_state), span.sinto(&self.hax_state)))
                .collect();
            non_trait_preds
        };

        let predicates: Vec<(hax::Predicate, hax::Span)> = trait_preds
            .into_iter()
            .chain(non_trait_preds.into_iter())
            .collect();
        trace!("Predicates of {:?}\n{:?}", def_id, predicates);
        hax::GenericPredicates { parent, predicates }
    }

    /// This function should be called **after** we translated the generics
    /// (type parameters, regions...).
    ///
    /// [parent_predicates_as_parent_clauses]: if [Some], the predicates
    /// of the parent must be registered as parent clauses.
    pub(crate) fn translate_predicates_of(
        &mut self,
        parent_trait_id: Option<TraitDeclId::Id>,
        def_id: DefId,
    ) -> Result<(), Error> {
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

                if let Some(trait_id) = parent_trait_id {
                    self.with_parent_trait_clauses(
                        TraitInstanceId::SelfId,
                        trait_id,
                        &mut |ctx: &mut Self| ctx.translate_predicates(&preds),
                    )?;
                } else {
                    self.translate_predicates(&preds)?;
                }
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
        self.translate_predicates(&preds)?;

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
        Ok(())
    }

    /// Translate the predicates then solve the unsolved trait obligations
    /// in the registered trait clauses.
    pub(crate) fn translate_predicates_solve_trait_obligations_of(
        &mut self,
        parent_trait_id: Option<TraitDeclId::Id>,
        def_id: DefId,
    ) -> Result<(), Error> {
        self.while_registering_trait_clauses(&mut |ctx| {
            ctx.translate_predicates_of(parent_trait_id, def_id)?;
            ctx.solve_trait_obligations_in_trait_clauses();
            Ok(())
        })
    }

    pub(crate) fn translate_predicates(
        &mut self,
        preds: &hax::GenericPredicates,
    ) -> Result<(), Error> {
        self.translate_predicates_vec(&preds.predicates)
    }

    pub(crate) fn translate_predicates_vec(
        &mut self,
        preds: &Vec<(hax::Predicate, hax::Span)>,
    ) -> Result<(), Error> {
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
            match self.translate_predicate(pred, span)? {
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
        Ok(())
    }

    /// Returns an [Option] because we may filter clauses about builtin or
    /// auto traits like [core::marker::Sized] and [core::marker::Sync].
    ///
    /// TODO: This function is used (among other things) to save trait clauses in the
    /// context, so that we can use them when solving the trait obligations which depend
    /// on the trait parameters. In order to make the resolution truly work, we should
    /// (give the possibility of) normalizing the types.
    pub(crate) fn translate_trait_clause(
        &mut self,
        hspan: &hax::Span,
        trait_pred: &hax::TraitPredicate,
    ) -> Result<Option<NonLocalTraitClause>, Error> {
        // Note sure what this is about
        assert!(trait_pred.is_positive);
        let span = hspan.rust_span;

        // We translate trait clauses for signatures, etc. so we do not erase the regions
        let erase_regions = false;

        let trait_ref = &trait_pred.trait_ref;
        let trait_id = self.translate_trait_decl_id(trait_ref.def_id.rust_def_id.unwrap());
        // We might have to ignore the trait
        let trait_id = if let Some(trait_id) = trait_id {
            trait_id
        } else {
            return Ok(None);
        };

        let (regions, types, const_generics) =
            self.translate_substs(span, erase_regions, None, &trait_ref.generic_args)?;
        // There are no trait refs
        let generics = GenericArgs::new(regions, types, const_generics, Vec::new());

        // Compute the current clause id
        let clause_id = (self.trait_instance_id_gen)();
        let meta = self.translate_meta_from_rspan(hspan.clone());

        // Immediately register the clause (we may need to refer to it in the parent/
        // item clauses)
        let trait_clause = NonLocalTraitClause {
            clause_id: clause_id.clone(),
            meta: Some(meta),
            trait_id,
            generics,
        };
        self.trait_clauses
            .insert(trait_clause.clause_id.clone(), trait_clause.clone());

        // [translate_trait_clause] takes care of registering the clause
        let _parent_clauses: Vec<_> =
            self.with_parent_trait_clauses(clause_id.clone(), trait_id, &mut |ctx: &mut Self| {
                trait_pred
                    .parent_preds
                    .iter()
                    .map(|x|
                      // TODO: the span information is not correct
                      ctx.translate_trait_clause(hspan, x))
                    .try_collect()
            })?;

        // [translate_trait_clause] takes care of registering the clause
        let _items_clauses: Vec<_> = trait_pred
            .items_preds
            .iter()
            .map(|(name, clauses)| {
                let clauses: Vec<_> = self.with_item_trait_clauses(
                    clause_id.clone(),
                    trait_id,
                    name.clone(),
                    &mut |ctx: &mut Self| {
                        clauses
                            .iter()
                            .map(|clause| {
                                // The clause is inside a binder
                                assert!(clause.bound_vars.is_empty());
                                // TODO: the span is not correct
                                ctx.translate_trait_clause(hspan, &clause.value)
                            })
                            .try_collect()
                    },
                )?;
                Ok((TraitItemName(name.to_string()), clauses))
            })
            .try_collect()?;

        // Return
        Ok(Some(trait_clause))
    }

    pub(crate) fn translate_predicate(
        &mut self,
        pred: &hax::Predicate,
        hspan: &hax::Span,
    ) -> Result<Option<Predicate>, Error> {
        trace!("{:?}", pred);
        // Predicates are always used in signatures/type definitions, etc.
        // For this reason, we do not erase the regions.
        let erase_regions = false;
        let span = hspan.rust_span;

        // Skip the binder (which lists the quantified variables).
        // By doing so, we allow the predicates to contain DeBruijn indices,
        // but it is ok because we only do a simple check.
        let pred_kind = &pred.value;
        use hax::{Clause, PredicateKind};
        match pred_kind {
            PredicateKind::Clause(Clause::Trait(trait_pred)) => Ok(self
                .translate_trait_clause(hspan, trait_pred)?
                .map(Predicate::Trait)),
            PredicateKind::Clause(Clause::RegionOutlives(p)) => {
                let r0 = self.translate_region(span, erase_regions, &p.0)?;
                let r1 = self.translate_region(span, erase_regions, &p.1)?;
                Ok(Some(Predicate::RegionOutlives(OutlivesPred(r0, r1))))
            }
            PredicateKind::Clause(Clause::TypeOutlives(p)) => {
                let ty = self.translate_ty(span, erase_regions, &p.0)?;
                let r = self.translate_region(span, erase_regions, &p.1)?;
                Ok(Some(Predicate::TypeOutlives(OutlivesPred(ty, r))))
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

                let trait_ref =
                    self.translate_trait_impl_source(span, erase_regions, impl_source)?;
                // The trait ref should be Some(...): the marker traits (that
                // we may filter) don't have associated types.
                let trait_ref = trait_ref.unwrap();

                let (regions, types, const_generics) = self
                    .translate_substs(span, erase_regions, None, substs)
                    .unwrap();
                let generics = GenericArgs {
                    regions,
                    types,
                    const_generics,
                    trait_refs: Vec::new(),
                };
                let ty = self.translate_ty(span, erase_regions, ty).unwrap();
                let type_name = TraitItemName(type_name.clone());
                Ok(Some(Predicate::TraitType(TraitTypeConstraint {
                    trait_ref,
                    generics,
                    type_name,
                    ty,
                })))
            }
            PredicateKind::Clause(Clause::ConstArgHasType(..)) => {
                // I don't really understand that one. Why don't they put
                // the type information in the const generic parameters
                // directly? For now we just ignore it.
                Ok(None)
            }
            PredicateKind::WellFormed(_) => error_or_panic!(
                self,
                span,
                format!("Unsupported predicate: {:?}", pred_kind)
            ),
            PredicateKind::ObjectSafe(_) => error_or_panic!(
                self,
                span,
                format!("Unsupported predicate: {:?}", pred_kind)
            ),
            PredicateKind::ClosureKind(_, _, _) => error_or_panic!(
                self,
                span,
                format!("Unsupported predicate: {:?}", pred_kind)
            ),
            PredicateKind::Subtype(_) => error_or_panic!(
                self,
                span,
                format!("Unsupported predicate: {:?}", pred_kind)
            ),
            PredicateKind::Coerce(_) => error_or_panic!(
                self,
                span,
                format!("Unsupported predicate: {:?}", pred_kind)
            ),
            PredicateKind::ConstEvaluatable(_) => error_or_panic!(
                self,
                span,
                format!("Unsupported predicate: {:?}", pred_kind)
            ),
            PredicateKind::ConstEquate(_, _) => error_or_panic!(
                self,
                span,
                format!("Unsupported predicate: {:?}", pred_kind)
            ),
            PredicateKind::TypeWellFormedFromEnv(_) => error_or_panic!(
                self,
                span,
                format!("Unsupported predicate: {:?}", pred_kind)
            ),
            PredicateKind::Ambiguous => error_or_panic!(
                self,
                span,
                format!("Unsupported predicate: {:?}", pred_kind)
            ),
            PredicateKind::AliasRelate(..) => error_or_panic!(
                self,
                span,
                format!("Unsupported predicate: {:?}", pred_kind)
            ),
        }
    }

    pub(crate) fn translate_trait_impl_sources(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        impl_sources: &Vec<hax::ImplSource>,
    ) -> Result<Vec<TraitRef>, Error> {
        let res: Vec<_> = impl_sources
            .iter()
            .map(|x| self.translate_trait_impl_source(span, erase_regions, x))
            .try_collect()?;
        Ok(res.into_iter().filter_map(|x| x).collect())
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn translate_trait_impl_source(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        impl_source: &hax::ImplSource,
    ) -> Result<Option<TraitRef>, Error> {
        let trait_decl_ref = {
            let trait_ref = &impl_source.trait_ref;
            let trait_id = self.translate_trait_decl_id(trait_ref.def_id.rust_def_id.unwrap());
            let trait_id = if let Some(trait_id) = trait_id {
                trait_id
            } else {
                return Ok(None);
            };

            let parent_trait_refs = Vec::new();
            let generics = self.translate_substs_and_trait_refs(
                span,
                erase_regions,
                None,
                &trait_ref.generic_args,
                &parent_trait_refs,
            )?;
            TraitDeclRef { trait_id, generics }
        };

        match self.translate_trait_impl_source_aux(
            span,
            erase_regions,
            impl_source,
            trait_decl_ref.clone(),
        ) {
            Ok(res) => Ok(res),
            Err(err) => {
                if !self.t_ctx.continue_on_failure {
                    panic!("Error during trait resolution: {}", err.msg)
                } else {
                    let msg = format!("Error during trait resolution: {}", &err.msg);
                    self.span_err(span, &msg);
                    let trait_id = TraitInstanceId::Unknown(err.msg);
                    Ok(Some(TraitRef {
                        trait_id,
                        generics: GenericArgs::empty(),
                        trait_decl_ref,
                    }))
                }
            }
        }
    }

    pub(crate) fn translate_trait_impl_source_aux(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        impl_source: &hax::ImplSource,
        trait_decl_ref: TraitDeclRef,
    ) -> Result<Option<TraitRef>, Error> {
        // TODO: in the body of this function:
        trace!("impl_source: {:?}", impl_source);
        use hax::ImplSourceKind;

        let trait_ref = match &impl_source.kind {
            ImplSourceKind::UserDefined(data) => {
                let def_id = data.impl_def_id.rust_def_id.unwrap();
                let trait_id = self.translate_trait_impl_id(def_id);
                // We already tested above whether the trait should be filtered
                let trait_id = trait_id.unwrap();
                let trait_id = TraitInstanceId::TraitImpl(trait_id);

                let generics = self.translate_substs_and_trait_refs(
                    span,
                    erase_regions,
                    None,
                    &data.substs,
                    &data.nested,
                )?;
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
                let generics = self.translate_substs_and_trait_refs(
                    span,
                    erase_regions,
                    None,
                    &trait_ref.generic_args,
                    trait_refs,
                )?;
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
            ImplSourceKind::Object(_) => {
                error_or_panic!(self, span, "Unsupported trait impl source kind: object")
            }
            ImplSourceKind::Builtin(trait_ref, traits) => {
                assert!(trait_ref.bound_vars.is_empty());
                let trait_ref = &trait_ref.value;
                let def_id = trait_ref.def_id.rust_def_id.unwrap();
                // Remark: we already filtered the marker traits when translating
                // the trait decl ref: the trait id should be Some(...).
                let trait_id = self.translate_trait_decl_id(def_id).unwrap();

                let trait_id = TraitInstanceId::BuiltinOrAuto(trait_id);
                let generics = self.translate_substs_and_trait_refs(
                    span,
                    erase_regions,
                    None,
                    &trait_ref.generic_args,
                    traits,
                )?;
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
                let ty = self.translate_ty(span, erase_regions, &data.fn_ty)?;
                let trait_id = TraitInstanceId::FnPointer(Box::new(ty));
                let trait_refs =
                    self.translate_trait_impl_sources(span, erase_regions, &data.nested)?;
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
            ImplSourceKind::Closure(_) => {
                let error = "Closures are not supported yet".to_string();
                self.span_err(span, &error);
                if !self.t_ctx.continue_on_failure {
                    panic!("{}", error)
                } else {
                    let trait_id = TraitInstanceId::Unknown(error);
                    TraitRef {
                        trait_id,
                        generics: GenericArgs::empty(),
                        trait_decl_ref,
                    }
                }
            }
            ImplSourceKind::TraitUpcasting(_) => unimplemented!(),
            ImplSourceKind::Error(msg) | ImplSourceKind::Todo(msg) => {
                let error = format!("Error during trait resolution: {}", msg);
                self.span_err(span, &error);
                if !self.t_ctx.continue_on_failure {
                    panic!("{}", error)
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
        Ok(Some(trait_ref))
    }

    fn match_trait_clauses(
        &self,
        trait_id: TraitDeclId::Id,
        generics: &GenericArgs,
        clause: &NonLocalTraitClause,
    ) -> bool {
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

            let src_types = &clause.generics.types;
            let src_const_generics = &clause.generics.const_generics;

            // We simply check the equality between the arguments:
            // there are no universally quantified variables to unify.
            // TODO: normalize the trait clauses (we actually
            // need to check equality **modulo** equality clauses)
            // TODO: if we need to unify (later, when allowing universal
            // quantification over clause parameters), use types_utils::TySubst.
            let matched = src_types == tgt_types && src_const_generics == tgt_const_generics;
            trace!("Match successful: {}", matched);
            matched
        }
    }

    /// Find the trait instance fullfilling a trait obligation.
    /// TODO: having to do this is very annoying. Isn't there a better way?
    fn find_trait_clause_for_param(
        &self,
        trait_id: TraitDeclId::Id,
        generics: &GenericArgs,
    ) -> TraitInstanceId {
        trace!(
            "Inside context of: {:?}\nSpan: {:?}",
            self.def_id,
            self.t_ctx.tcx.def_ident_span(self.def_id)
        );

        // Simply explore the trait clauses
        for trait_clause in self.trait_clauses.values() {
            if self.match_trait_clauses(trait_id, generics, trait_clause) {
                return trait_clause.clause_id.clone();
            }
        }

        // Could not find a clause.
        // Check if we are in the registration process, otherwise report an error.
        // TODO: we might be registering a where clause.
        if self.registering_trait_clauses {
            TraitInstanceId::Unsolved(trait_id, generics.clone())
        } else {
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

            if !self.t_ctx.continue_on_failure {
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
    }
}

struct TraitInstancesSolver<'a, 'tcx, 'ctx, 'ctx1> {
    /// The number of unsolved trait instances. This allows us to check whether we reached
    /// a fixed point or not (so that we don't enter infinite loops if we fail to solve
    /// some instances).
    pub unsolved_count: usize,
    /// The unsolved clauses.
    pub unsolved: Vec<(TraitDeclId::Id, GenericArgs)>,
    /// The current context
    pub ctx: &'a mut BodyTransCtx<'tcx, 'ctx, 'ctx1>,
}

impl<'a, 'tcx, 'ctx, 'ctx1> MutTypeVisitor for TraitInstancesSolver<'a, 'tcx, 'ctx, 'ctx1> {
    /// If we find an unsolved trait instance id, attempt to solve it
    fn visit_trait_instance_id(&mut self, id: &mut TraitInstanceId) {
        if let TraitInstanceId::Unsolved(trait_id, generics) = id {
            let solved_id = self.ctx.find_trait_clause_for_param(*trait_id, generics);

            if let TraitInstanceId::Unsolved(..) = solved_id {
                // Failure: increment the unsolved count
                self.unsolved_count += 1;
            } else {
                // Success: replace
                *id = solved_id;
            }
        } else {
            MutTypeVisitor::default_visit_trait_instance_id(self, id);
        }
    }
}

impl<'a, 'tcx, 'ctx, 'ctx1> SharedTypeVisitor for TraitInstancesSolver<'a, 'tcx, 'ctx, 'ctx1> {
    /// If we find an unsolved trait instance id, save it
    fn visit_trait_instance_id(&mut self, id: &TraitInstanceId) {
        if let TraitInstanceId::Unsolved(trait_id, generics) = id {
            self.unsolved.push((*trait_id, generics.clone()))
        } else {
            SharedTypeVisitor::default_visit_trait_instance_id(self, id);
        }
    }
}

impl<'a, 'tcx, 'ctx, 'ctx1> TraitInstancesSolver<'a, 'tcx, 'ctx, 'ctx1> {
    /// Auxiliary function
    fn visit(&mut self, solve: bool) {
        // For now we clone the trait clauses map - we will make it more effcicient later
        let mut trait_clauses: Vec<(TraitInstanceId, NonLocalTraitClause)> = self
            .ctx
            .trait_clauses
            .iter()
            .map(|(id, c)| (id.clone(), c.clone()))
            .collect();
        for (_, clause) in trait_clauses.iter_mut() {
            if solve {
                MutTypeVisitor::visit_trait_instance_id(self, &mut clause.clause_id);
                MutTypeVisitor::visit_generic_args(self, &mut clause.generics);
            } else {
                SharedTypeVisitor::visit_trait_instance_id(self, &clause.clause_id);
                SharedTypeVisitor::visit_generic_args(self, &clause.generics);
            }
        }

        // If we are solving: reconstruct the trait clauses map, and replace the one in the context
        if solve {
            self.ctx.trait_clauses = im::OrdMap::from(trait_clauses);
        }
        // Otherwise: also collect the unsolved proof obligations in the predicates
        // which are not trait predicates
        else {
            // TODO: annoying that we have to clone
            for x in &self.ctx.types_outlive.clone() {
                SharedTypeVisitor::visit_type_outlives(self, x);
            }
            // TODO: annoying that we have to clone
            for x in &self.ctx.trait_type_constraints.clone() {
                SharedTypeVisitor::visit_trait_type_constraint(self, x);
            }
        }
    }

    /// Perform one pass of solving the trait obligations
    fn solve_one_pass(&mut self) {
        self.unsolved_count = 0;
        self.visit(true);
    }

    fn collect_unsolved(&mut self) {
        self.visit(false);
    }

    /// While there are unsolved trait obligations in the registered trait
    /// clauses, solve them (unless we get stuck).
    pub(crate) fn solve_repeat(&mut self) {
        self.solve_one_pass();

        let mut count = self.unsolved_count;
        let mut pass_id = 0;
        while count > 0 {
            log::trace!("Pass id: {}, unsolved count: {}", pass_id, count);
            self.solve_one_pass();
            if self.unsolved_count >= count {
                // We're stuck: report an error

                // Retraverse the context, collecting the unsolved clauses.
                self.collect_unsolved();

                let unsolved = self
                    .unsolved
                    .iter()
                    .map(|(trait_id, generics)| {
                        format!(
                            "{}{}",
                            self.ctx.format_object(*trait_id),
                            generics.fmt_with_ctx(&*self.ctx)
                        )
                    })
                    .collect::<Vec<String>>()
                    .join("\n");
                let clauses = self
                    .ctx
                    .trait_clauses
                    .values()
                    .map(|x| x.fmt_with_ctx(&*self.ctx))
                    .collect::<Vec<String>>()
                    .join("\n");

                if !self.ctx.t_ctx.continue_on_failure {
                    unreachable!(
                        "Could not find clauses for trait obligations:{}\n\nAvailable clauses:\n{}\n- context: {:?}",
                        unsolved, clauses, self.ctx.def_id
                    );
                } else {
                    // Simply log a warning
                    log::warn!(
                        "Could not find clauses for trait obligations:{}\n\nAvailable clauses:\n{}\n- context: {:?}",
                        unsolved, clauses, self.ctx.def_id
                    );
                }

                return;
            } else {
                // We made progress: update the count
                count = self.unsolved_count;
                pass_id += 1;
            }
        }

        // We're done: check the where clauses which are not trait predicates
        self.collect_unsolved();
        assert!(self.unsolved.is_empty());
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Solve the unsolved trait obligations in the trait clauses (some clauses
    /// may refer to other clauses, meaning that we are not necessarily able
    /// to solve all the trait obligations when registering a clause, but might
    /// be able later).
    pub(crate) fn solve_trait_obligations_in_trait_clauses(&mut self) {
        let mut solver = TraitInstancesSolver {
            unsolved_count: 0,
            unsolved: Vec::new(),
            ctx: self,
        };

        solver.solve_repeat()
    }
}
