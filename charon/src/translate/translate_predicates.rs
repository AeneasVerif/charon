use crate::common::*;
use crate::formatter::Formatter;
use crate::formatter::IntoFormatter;
use crate::gast::*;
use crate::meta::Span;
use crate::pretty::FmtWithCtx;
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
    pub span: Option<Span>,
    pub origin: PredicateOrigin,
    pub trait_id: TraitDeclId,
    pub generics: GenericArgs,
}

impl NonLocalTraitClause {
    pub(crate) fn to_trait_clause_with_id(&self, clause_id: TraitClauseId) -> TraitClause {
        TraitClause {
            clause_id,
            origin: self.origin.clone(),
            span: self.span,
            trait_id: self.trait_id,
            generics: self.generics.clone(),
        }
    }
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, EnumToGetters)]
pub(crate) enum Predicate {
    Trait(#[expect(dead_code)] TraitClauseId),
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

    pub(crate) fn get_parent_params_info(
        &mut self,
        def_id: DefId,
    ) -> Result<Option<ParamsInfo>, Error> {
        let params_info =
            hax::get_parent_params_info(&self.hax_state, def_id).map(Self::convert_params_info);

        // Very annoying: because we may filter some marker traits (like [core::marker::Sized])
        // we have to recompute the number of trait clauses!
        let info = match params_info {
            None => None,
            Some(mut params_info) => {
                let tcx = self.t_ctx.tcx;
                let parent_id = tcx.generics_of(def_id).parent.unwrap();

                let mut num_trait_clauses = 0;
                // **IMPORTANT**: we do NOT want to use [TyCtxt::predicates_of].
                let preds = tcx.predicates_defined_on(parent_id).sinto(&self.hax_state);
                for (pred, span) in preds.predicates {
                    if let hax::PredicateKind::Clause(hax::ClauseKind::Trait(clause)) =
                        &pred.kind.value
                    {
                        if self
                            .register_trait_decl_id(
                                span.rust_span_data.unwrap().span(),
                                DefId::from(&clause.trait_ref.def_id),
                            )?
                            .is_some()
                        {
                            num_trait_clauses += 1;
                        }
                    }
                }
                params_info.num_trait_clauses = num_trait_clauses;
                Some(params_info)
            }
        };
        Ok(info)
    }

    pub(crate) fn get_predicates_of(
        &mut self,
        def_id: DefId,
    ) -> Result<hax::GenericPredicates, Error> {
        // **IMPORTANT**:
        // There are two functions which allow to retrieve the predicates of
        // a definition:
        // - [TyCtxt::predicates_defined_on]: returns exactly the list of predicates
        //   that the user has written on the definition:
        //   FIXME: today's docs say that these includes `outlives` predicates as well
        // - [TyCtxt::predicates_of]: returns the user defined predicates and also:
        //   - if called on a trait `Foo`, we get an additional trait clause
        //     `Self : Foo` (i.e., the trait requires itself), which is not what we want.
        //   - for the type definitions, it also returns additional type/region outlives
        //     information, which the user doesn't have to write by hand (but it doesn't
        //     add those for functions). For instance, below:
        //     ```
        //     struct MutMut<'a, 'b, T> {
        //         x: &'a mut &'b mut T,
        //     }
        //     ```
        //     The rust compiler adds the predicates: `'b: 'a` ('b outlives 'a) and `T: 'b`.
        // For this reason we:
        // - retrieve the trait predicates with [TyCtxt::predicates_defined_on]
        // - retrieve the other predicates with [TyCtxt::predicates_of]
        //
        // Also, we reorder the predicates to make sure that the trait clauses come
        // *before* the other clauses. This helps, when translating, with having the trait clauses
        // in the context if we need them.
        //
        // Example:
        // ```
        // fn f<T: Foo<S = U::S>, U: Foo>(...)
        //                 ^^^^ must make sure we have U: Foo in the context
        //                      before translating this
        // ```
        // There's no perfect ordering though, as this shows:
        // ```
        // fn f<T: Foo<U::S>, U: Foo<T::S>>(...)
        //                           ^^^^ we'd need to have T: Foo in the context
        //                                before translating this
        //             ^^^^ we'd need to have U: Foo in the context
        //                  before translating this
        // ```
        let tcx = self.t_ctx.tcx;
        let param_env = tcx.param_env(def_id);
        let parent: Option<hax::DefId>;

        let trait_preds = {
            // Remark: we don't convert the predicates yet because we need to
            // normalize them before.
            let predicates = tcx.predicates_defined_on(def_id);
            parent = predicates.parent.sinto(&self.hax_state);
            let clauses: Vec<&(rustc_middle::ty::Clause<'_>, rustc_span::Span)> =
                predicates.predicates.iter().collect();
            trace!(
                "TyCtxt::predicates_defined_on({:?}):\n{:?}",
                def_id,
                clauses
            );

            let trait_clauses: Vec<&(rustc_middle::ty::Clause<'_>, rustc_span::Span)> = clauses
                .into_iter()
                .filter(|x| {
                    matches!(
                        &x.0.kind().skip_binder(),
                        rustc_middle::ty::ClauseKind::Trait(_)
                    )
                })
                .collect();

            let trait_preds: Vec<(hax::Predicate, hax::Span)> = trait_clauses
                .into_iter()
                .map(|(clause, span)| {
                    if clause.kind().no_bound_vars().is_none() {
                        // Report an error
                        error_or_panic!(self, *span, "Predicates with bound regions (i.e., `for<'a> ...`) are not supported yet")
                    }
                    // Normalize the trait clause
                    let pred = tcx.normalize_erasing_regions(param_env, clause.as_predicate());
                    Ok((pred.sinto(&self.hax_state), span.sinto(&self.hax_state)))
                })
                .try_collect()?;

            trait_preds
        };

        let non_trait_preds = {
            let predicates = tcx.predicates_of(def_id);
            let predicates: Vec<&(rustc_middle::ty::Clause<'_>, rustc_span::Span)> =
                predicates.predicates.iter().collect();
            trace!("TyCtxt::predicates_of({:?}):\n{:?}", def_id, predicates);

            let non_trait_preds: Vec<&(rustc_middle::ty::Clause<'_>, rustc_span::Span)> =
                predicates
                    .into_iter()
                    .filter(|x| {
                        !(matches!(
                            &x.0.kind().skip_binder(),
                            rustc_middle::ty::ClauseKind::Trait(_)
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
                .map(|(pred, span)| {
                    (
                        pred.as_predicate().sinto(&self.hax_state),
                        span.sinto(&self.hax_state),
                    )
                })
                .collect();
            non_trait_preds
        };

        let predicates: Vec<(hax::Predicate, hax::Span)> = trait_preds
            .into_iter()
            .chain(non_trait_preds.into_iter())
            .collect();
        trace!("Predicates of {:?}\n{:?}", def_id, predicates);
        Ok(hax::GenericPredicates { parent, predicates })
    }

    /// This function should be called **after** we translated the generics
    /// (type parameters, regions...).
    ///
    /// [parent_predicates_as_parent_clauses]: if [Some], the predicates
    /// of the parent must be registered as parent clauses.
    pub(crate) fn translate_predicates_of(
        &mut self,
        parent_trait_id: Option<TraitDeclId>,
        def_id: DefId,
        origin: PredicateOrigin,
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
                let preds = self.get_predicates_of(parent_id)?;
                trace!("Predicates of parent ({:?}): {:?}", parent_id, preds);

                if let Some(trait_id) = parent_trait_id {
                    self.with_parent_trait_clauses(trait_id, |ctx: &mut Self| {
                        // TODO: distinguish where clauses from supertraits.
                        ctx.translate_predicates(&preds, PredicateOrigin::WhereClauseOnTrait)
                    })?;
                } else {
                    self.translate_predicates(&preds, PredicateOrigin::WhereClauseOnImpl)?;
                }
            }
        }

        let fmt_ctx = self.into_fmt();
        let clauses = self
            .trait_clauses
            .values()
            .flat_map(|x| x)
            .map(|c| c.fmt_with_ctx(&fmt_ctx))
            .collect::<Vec<String>>()
            .join(",\n");
        trace!(
            "Local trait clauses of {:?} after translating the predicates of the parent:\n{}",
            def_id,
            clauses
        );

        // The predicates of the current definition
        let preds = self.get_predicates_of(def_id)?;
        trace!("Local predicates of {:?}:\n{:?}", def_id, preds);
        self.translate_predicates(&preds, origin)?;

        let fmt_ctx = self.into_fmt();
        let clauses = self
            .trait_clauses
            .values()
            .flat_map(|x| x)
            .map(|c| c.fmt_with_ctx(&fmt_ctx))
            .collect::<Vec<String>>()
            .join(",\n");
        trace!(
            "All trait clauses of {:?} (parents + locals):\n{}",
            def_id,
            clauses
        );
        Ok(())
    }

    pub(crate) fn translate_predicates(
        &mut self,
        preds: &hax::GenericPredicates,
        origin: PredicateOrigin,
    ) -> Result<(), Error> {
        self.translate_predicates_vec(&preds.predicates, origin)
    }

    pub(crate) fn translate_predicates_vec(
        &mut self,
        preds: &Vec<(hax::Predicate, hax::Span)>,
        origin: PredicateOrigin,
    ) -> Result<(), Error> {
        trace!("Predicates:\n{:?}", preds);
        for (pred, span) in preds {
            match self.translate_predicate(pred, span, origin.clone())? {
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

    /// Returns an [Option] because we may filter trait refs about builtin or
    /// auto traits like [core::marker::Sized] and [core::marker::Sync].
    pub(crate) fn translate_trait_decl_ref(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        trait_ref: &hax::TraitRef,
    ) -> Result<Option<TraitDeclRef>, Error> {
        let trait_id = self.register_trait_decl_id(span, DefId::from(&trait_ref.def_id))?;
        // We might have to ignore the trait
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
        Ok(Some(TraitDeclRef { trait_id, generics }))
    }

    /// Returns an [Option] because we may filter clauses about builtin or
    /// auto traits like [core::marker::Sized] and [core::marker::Sync].
    ///
    /// `origin` is where this clause comes from.
    pub(crate) fn translate_trait_clause(
        &mut self,
        hspan: &hax::Span,
        trait_pred: &hax::TraitPredicate,
        origin: PredicateOrigin,
    ) -> Result<Option<TraitClauseId>, Error> {
        // FIXME: once `clause` can't be `None`, use `Vector::reserve_slot` to be sure we don't use
        // the same id twice.
        let (clause_id, instance_id) = self.clause_translation_context.generate_instance_id();
        let clause = self.translate_trait_clause_aux(hspan, trait_pred, instance_id, origin)?;
        if let Some(clause) = clause {
            let local_clause = clause.to_trait_clause_with_id(clause_id);
            self.clause_translation_context
                .as_mut_clauses()
                .push(local_clause);
            self.trait_clauses
                .entry(clause.trait_id)
                .or_default()
                .push(clause);
            Ok(Some(clause_id))
        } else {
            Ok(None)
        }
    }

    /// Returns an [Option] because we may filter clauses about builtin or
    /// auto traits like [core::marker::Sized] and [core::marker::Sync].
    pub(crate) fn translate_self_trait_clause(
        &mut self,
        span: &hax::Span,
        trait_pred: &hax::TraitPredicate,
    ) -> Result<(), Error> {
        // Save the self clause (and its parent/item clauses)
        let clause = self.translate_trait_clause_aux(
            span,
            &trait_pred,
            TraitInstanceId::SelfId,
            PredicateOrigin::TraitSelf,
        )?;
        if let Some(clause) = clause {
            self.trait_clauses
                .entry(clause.trait_id)
                .or_default()
                .push(clause);
        }
        Ok(())
    }

    pub(crate) fn translate_trait_clause_aux(
        &mut self,
        hspan: &hax::Span,
        trait_pred: &hax::TraitPredicate,
        clause_id: TraitInstanceId,
        origin: PredicateOrigin,
    ) -> Result<Option<NonLocalTraitClause>, Error> {
        // Note sure what this is about
        assert!(trait_pred.is_positive);
        let span = hspan.rust_span_data.unwrap().span();

        // We translate trait clauses for signatures, etc. so we do not erase the regions
        let erase_regions = false;

        let trait_ref = &trait_pred.trait_ref;
        let trait_id = self.register_trait_decl_id(span, DefId::from(&trait_ref.def_id))?;
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

        let span = self.translate_span_from_rspan(hspan.clone());

        Ok(Some(NonLocalTraitClause {
            clause_id,
            span: Some(span),
            origin,
            trait_id,
            generics,
        }))
    }

    pub(crate) fn translate_predicate(
        &mut self,
        pred: &hax::Predicate,
        hspan: &hax::Span,
        origin: PredicateOrigin,
    ) -> Result<Option<Predicate>, Error> {
        trace!("{:?}", pred);
        // Predicates are always used in signatures/type definitions, etc.
        // For this reason, we do not erase the regions.
        let erase_regions = false;
        let span = hspan.rust_span_data.unwrap().span();

        // Skip the binder (which lists the quantified variables).
        // By doing so, we allow the predicates to contain DeBruijn indices,
        // but it is ok because we only do a simple check.
        let pred_kind = &pred.kind.value;
        use hax::{ClauseKind, PredicateKind};
        match pred_kind {
            PredicateKind::Clause(kind) => {
                match kind {
                    ClauseKind::Trait(trait_pred) => Ok(self
                        .translate_trait_clause(hspan, trait_pred, origin)?
                        .map(Predicate::Trait)),
                    ClauseKind::RegionOutlives(p) => {
                        let r0 = self.translate_region(span, erase_regions, &p.lhs)?;
                        let r1 = self.translate_region(span, erase_regions, &p.rhs)?;
                        Ok(Some(Predicate::RegionOutlives(OutlivesPred(r0, r1))))
                    }
                    ClauseKind::TypeOutlives(p) => {
                        let ty = self.translate_ty(span, erase_regions, &p.lhs)?;
                        let r = self.translate_region(span, erase_regions, &p.rhs)?;
                        Ok(Some(Predicate::TypeOutlives(OutlivesPred(ty, r))))
                    }
                    ClauseKind::Projection(p) => {
                        // This is used to express constraints over associated types.
                        // For instance:
                        // ```
                        // T : Foo<S = String>
                        //         ^^^^^^^^^^
                        // ```
                        let hax::ProjectionPredicate {
                            impl_expr,
                            assoc_item,
                            ty,
                        } = p;

                        let trait_ref =
                            self.translate_trait_impl_expr(span, erase_regions, impl_expr)?;
                        // The trait ref should be Some(...): the marker traits (that
                        // we may filter) don't have associated types.
                        let trait_ref = trait_ref.unwrap();
                        let ty = self.translate_ty(span, erase_regions, ty).unwrap();
                        let type_name = TraitItemName(assoc_item.name.clone().into());
                        Ok(Some(Predicate::TraitType(TraitTypeConstraint {
                            trait_ref,
                            type_name,
                            ty,
                        })))
                    }
                    ClauseKind::ConstArgHasType(..) => {
                        // I don't really understand that one. Why don't they put
                        // the type information in the const generic parameters
                        // directly? For now we just ignore it.
                        Ok(None)
                    }
                    ClauseKind::WellFormed(_) | ClauseKind::ConstEvaluatable(_) => {
                        error_or_panic!(self, span, format!("Unsupported clause: {:?}", kind))
                    }
                }
            }
            PredicateKind::AliasRelate(..)
            | PredicateKind::Ambiguous
            | PredicateKind::Coerce(_)
            | PredicateKind::ConstEquate(_, _)
            | PredicateKind::ObjectSafe(_)
            | PredicateKind::NormalizesTo(_)
            | PredicateKind::Subtype(_) => error_or_panic!(
                self,
                span,
                format!("Unsupported predicate: {:?}", pred_kind)
            ),
        }
    }

    pub(crate) fn translate_trait_impl_exprs(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        impl_sources: &[hax::ImplExpr],
    ) -> Result<Vec<TraitRef>, Error> {
        let res: Vec<_> = impl_sources
            .iter()
            .map(|x| self.translate_trait_impl_expr(span, erase_regions, x))
            .try_collect()?;
        Ok(res.into_iter().flatten().collect())
    }

    /// Returns an [Option] because we may ignore some builtin or auto traits
    /// like [core::marker::Sized] or [core::marker::Sync].
    pub(crate) fn translate_trait_impl_expr(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        impl_expr: &hax::ImplExpr,
    ) -> Result<Option<TraitRef>, Error> {
        let trait_decl_ref =
            match self.translate_trait_decl_ref(span, erase_regions, &impl_expr.r#trait)? {
                None => return Ok(None),
                Some(tr) => tr,
            };

        match self.translate_trait_impl_expr_aux(
            span,
            erase_regions,
            impl_expr,
            trait_decl_ref.clone(),
        ) {
            Ok(res) => Ok(res),
            Err(err) => {
                if !self.t_ctx.continue_on_failure() {
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

    pub(crate) fn translate_trait_impl_expr_aux(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        impl_source: &hax::ImplExpr,
        trait_decl_ref: TraitDeclRef,
    ) -> Result<Option<TraitRef>, Error> {
        // TODO: in the body of this function:
        trace!("impl_source: {:?}", impl_source);
        use hax::ImplExprAtom;

        let nested = &impl_source.args;
        let trait_ref = match &impl_source.r#impl {
            ImplExprAtom::Concrete {
                id: impl_def_id,
                generics,
            } => {
                let def_id = DefId::from(impl_def_id);
                let trait_id = self.register_trait_impl_id(span, def_id)?;
                // We already tested above whether the trait should be filtered
                let trait_id = trait_id.unwrap();
                let trait_id = TraitInstanceId::TraitImpl(trait_id);

                let generics = self.translate_substs_and_trait_refs(
                    span,
                    erase_regions,
                    None,
                    generics,
                    nested,
                )?;
                TraitRef {
                    trait_id,
                    generics,
                    trait_decl_ref,
                }
            }
            // The self clause and the other clauses are handled in a similar manner
            ImplExprAtom::SelfImpl {
                r#trait: trait_ref,
                path,
            }
            | ImplExprAtom::LocalBound {
                predicate_id: _,
                r#trait: trait_ref,
                path,
            } => {
                // (trait_ref, trait_refs, constness)
                // TODO: the constness information is not there anymore...
                // Explanations about constness: https://stackoverflow.com/questions/70441495/what-is-impl-const-in-rust
                trace!(
                    "impl source (self or clause): param:\n- trait_ref: {:?}\n- path: {:?}",
                    trait_ref,
                    path,
                );
                assert!(trait_ref.bound_vars.is_empty());
                let trait_ref = &trait_ref.value;

                let def_id = DefId::from(&trait_ref.def_id);
                // Remark: we already filtered the marker traits when translating
                // the trait decl ref: the trait decl id should be Some(...).
                let trait_decl_id = self.register_trait_decl_id(span, def_id)?.unwrap();

                // Retrieve the arguments
                assert!(nested.is_empty());
                let generics = self.translate_substs_and_trait_refs(
                    span,
                    erase_regions,
                    None,
                    &trait_ref.generic_args,
                    nested,
                )?;

                // If we are refering to a trait clause, we need to find the
                // relevant one.
                let mut trait_id = match &impl_source.r#impl {
                    ImplExprAtom::SelfImpl { .. } => TraitInstanceId::SelfId,
                    ImplExprAtom::LocalBound { .. } => {
                        self.find_trait_clause_for_param(trait_decl_id, &generics)
                    }
                    _ => unreachable!(),
                };
                let mut current_trait_decl_id = trait_decl_id;

                // Apply the path
                for path_elem in path {
                    use hax::ImplExprPathChunk::*;
                    match path_elem {
                        AssocItem {
                            item,
                            predicate,
                            index,
                            predicate_id: _,
                        } => {
                            trait_id = TraitInstanceId::ItemClause(
                                Box::new(trait_id),
                                current_trait_decl_id,
                                TraitItemName(item.name.clone()),
                                TraitClauseId::new(*index),
                            );
                            current_trait_decl_id = self
                                .register_trait_decl_id(
                                    span,
                                    DefId::from(&predicate.value.trait_ref.def_id),
                                )?
                                .unwrap();
                        }
                        Parent {
                            predicate,
                            index,
                            predicate_id: _,
                        } => {
                            trait_id = TraitInstanceId::ParentClause(
                                Box::new(trait_id),
                                current_trait_decl_id,
                                TraitClauseId::new(*index),
                            );
                            current_trait_decl_id = self
                                .register_trait_decl_id(
                                    span,
                                    DefId::from(&predicate.value.trait_ref.def_id),
                                )?
                                .unwrap();
                        }
                    }
                }

                // Ignore the arguments: we forbid using universal quantifiers
                // on the trait clauses for now.
                TraitRef {
                    trait_id,
                    generics: GenericArgs::empty(),
                    trait_decl_ref,
                }
            }
            ImplExprAtom::Dyn => TraitRef {
                trait_id: TraitInstanceId::Dyn(trait_decl_ref.trait_id),
                generics: GenericArgs::empty(),
                trait_decl_ref,
            },
            ImplExprAtom::Builtin { r#trait: trait_ref } => {
                let def_id = DefId::from(&trait_ref.def_id);
                // Remark: we already filtered the marker traits when translating
                // the trait decl ref: the trait id should be Some(...).
                let trait_id = self.register_trait_decl_id(span, def_id)?.unwrap();

                let trait_id = TraitInstanceId::BuiltinOrAuto(trait_id);
                let generics = self.translate_substs_and_trait_refs(
                    span,
                    erase_regions,
                    None,
                    &trait_ref.generic_args,
                    nested,
                )?;
                TraitRef {
                    trait_id,
                    generics,
                    trait_decl_ref,
                }
            }
            ImplExprAtom::Todo(msg) => {
                let error = format!("Error during trait resolution: {}", msg);
                self.span_err(span, &error);
                if !self.t_ctx.continue_on_failure() {
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
        trait_id: TraitDeclId,
        generics: &GenericArgs,
        clause: &NonLocalTraitClause,
    ) -> bool {
        let fmt_ctx = self.into_fmt();
        trace!("Matching trait clauses:\n- trait_id: {:?}\n- generics: {:?}\n- clause.trait_id: {:?}\n- clause.generics: {:?}",
               fmt_ctx.format_object(trait_id), generics.fmt_with_ctx(&fmt_ctx),
               fmt_ctx.format_object(clause.trait_id), clause.generics.fmt_with_ctx(&fmt_ctx)
        );
        assert_eq!(clause.trait_id, trait_id);
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

    /// Find the trait instance fullfilling a trait obligation.
    /// TODO: having to do this is very annoying. Isn't there a better way?
    fn find_trait_clause_for_param(
        &self,
        trait_id: TraitDeclId,
        generics: &GenericArgs,
    ) -> TraitInstanceId {
        trace!(
            "Inside context of: {:?}\nSpan: {:?}",
            self.def_id,
            self.t_ctx.tcx.def_ident_span(self.def_id)
        );

        // Simply explore the trait clauses
        if let Some(clauses_for_this_trait) = self.trait_clauses.get(&trait_id) {
            for trait_clause in clauses_for_this_trait {
                if self.match_trait_clauses(trait_id, generics, trait_clause) {
                    return trait_clause.clause_id.clone();
                }
            }
        };

        // Could not find a clause.
        // Check if we are in the registration process, otherwise report an error.
        // TODO: we might be registering a where clause.
        let fmt_ctx = self.into_fmt();
        let trait_ref = format!(
            "{}{}",
            fmt_ctx.format_object(trait_id),
            generics.fmt_with_ctx(&fmt_ctx)
        );
        let clauses: Vec<String> = self
            .trait_clauses
            .values()
            .flat_map(|x| x)
            .map(|x| x.fmt_with_ctx(&fmt_ctx))
            .collect();

        if !self.t_ctx.continue_on_failure() {
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
