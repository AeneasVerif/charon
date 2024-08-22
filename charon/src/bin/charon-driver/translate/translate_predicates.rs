use super::translate_ctx::*;
use super::translate_traits::PredicateLocation;
use charon_lib::common::*;
use charon_lib::formatter::{AstFormatter, IntoFormatter};
use charon_lib::gast::*;
use charon_lib::ids::Vector;
use charon_lib::meta::Span;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::types::*;
use hax_frontend_exporter as hax;
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
    pub clause_id: TraitRefKind,
    /// [Some] if this is the top clause, [None] if this is about a parent/
    /// associated type clause.
    pub span: Option<Span>,
    pub origin: PredicateOrigin,
    pub trait_: TraitDeclRef,
}

impl NonLocalTraitClause {
    pub(crate) fn to_trait_clause_with_id(&self, clause_id: TraitClauseId) -> TraitClause {
        TraitClause {
            clause_id,
            origin: self.origin.clone(),
            span: self.span,
            trait_: self.trait_.clone(),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for NonLocalTraitClause {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let clause_id = self.clause_id.fmt_with_ctx(ctx);
        let trait_ = self.trait_.fmt_with_ctx(ctx);
        format!("[{clause_id}]: {trait_}")
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
    pub fn count_generics(
        &mut self,
        generics: &hax::TyGenerics,
        predicates: &hax::GenericPredicates,
    ) -> Result<ParamsInfo, Error> {
        use hax::ClauseKind;
        use hax::GenericParamDefKind;
        use hax::PredicateKind;
        let mut num_region_params = 0;
        let mut num_type_params = 0;
        let mut num_const_generic_params = 0;
        let mut num_trait_clauses = 0;
        let mut num_regions_outlive = 0;
        let mut num_types_outlive = 0;
        let mut num_trait_type_constraints = 0;

        for param in &generics.params {
            match param.kind {
                GenericParamDefKind::Lifetime => num_region_params += 1,
                GenericParamDefKind::Type { .. } => num_type_params += 1,
                GenericParamDefKind::Const { .. } => num_const_generic_params += 1,
            }
        }
        for (pred, _span) in &predicates.predicates {
            match &pred.kind.value {
                PredicateKind::Clause(ClauseKind::Trait(_)) => num_trait_clauses += 1,
                PredicateKind::Clause(ClauseKind::RegionOutlives(_)) => num_regions_outlive += 1,
                PredicateKind::Clause(ClauseKind::TypeOutlives(_)) => num_types_outlive += 1,
                PredicateKind::Clause(ClauseKind::Projection(_)) => num_trait_type_constraints += 1,
                _ => (),
            }
        }

        Ok(ParamsInfo {
            num_region_params,
            num_type_params,
            num_const_generic_params,
            num_trait_clauses,
            num_regions_outlive,
            num_types_outlive,
            num_trait_type_constraints,
        })
    }

    /// This function should be called **after** we translated the generics (type parameters,
    /// regions...).
    pub(crate) fn translate_predicates(
        &mut self,
        preds: &hax::GenericPredicates,
        origin: PredicateOrigin,
        location: &PredicateLocation,
    ) -> Result<(), Error> {
        // Translate the trait predicates first, because associated type constraints may refer to
        // them. E.g. in `fn foo<I: Iterator<Item=usize>>()`, the `I: Iterator` clause must be
        // translated before the `<I as Iterator>::Item = usize` predicate.
        for (pred, span) in &preds.predicates {
            if matches!(
                pred.kind.value,
                hax::PredicateKind::Clause(hax::ClauseKind::Trait(_))
            ) {
                // Don't need to do anything with the translated clause, it is already registered
                // in `self.trait_clauses`.
                let _ = self.translate_predicate(pred, span, origin.clone(), location)?;
            }
        }
        for (pred, span) in &preds.predicates {
            if !matches!(
                pred.kind.value,
                hax::PredicateKind::Clause(hax::ClauseKind::Trait(_))
            ) {
                match self.translate_predicate(pred, span, origin.clone(), location)? {
                    None => (),
                    Some(pred) => match pred {
                        Predicate::TypeOutlives(p) => self.types_outlive.push(p),
                        Predicate::RegionOutlives(p) => self.regions_outlive.push(p),
                        Predicate::TraitType(p) => self.trait_type_constraints.push(p),
                        Predicate::Trait(_) => unreachable!(),
                    },
                }
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
        let trait_id = self.register_trait_decl_id(span, DefId::from(&trait_ref.def_id));
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
        location: &PredicateLocation,
    ) -> Result<Option<TraitClauseId>, Error> {
        // FIXME: once `clause` can't be `None`, use `Vector::reserve_slot` to be sure we don't use
        // the same id twice.
        let clause_id = match location {
            PredicateLocation::Base => self.param_trait_clauses.next_id(),
            PredicateLocation::Parent(..) => self.parent_trait_clauses.next_id(),
            PredicateLocation::Item(.., item_name) => self
                .item_trait_clauses
                .entry(item_name.clone())
                .or_default()
                .next_id(),
        };
        let instance_id = match location {
            PredicateLocation::Base => TraitRefKind::Clause(clause_id),
            PredicateLocation::Parent(trait_decl_id) => TraitRefKind::ParentClause(
                Box::new(TraitRefKind::SelfId),
                *trait_decl_id,
                clause_id,
            ),
            PredicateLocation::Item(trait_decl_id, item_name) => TraitRefKind::ItemClause(
                Box::new(TraitRefKind::SelfId),
                *trait_decl_id,
                item_name.clone(),
                clause_id,
            ),
        };
        let clause = self.translate_trait_clause_aux(hspan, trait_pred, instance_id, origin)?;
        if let Some(clause) = clause {
            let local_clause = clause.to_trait_clause_with_id(clause_id);
            match location {
                PredicateLocation::Base => {
                    self.param_trait_clauses.push(local_clause);
                }
                PredicateLocation::Parent(..) => {
                    self.parent_trait_clauses.push(local_clause);
                }
                PredicateLocation::Item(.., item_name) => {
                    self.item_trait_clauses
                        .get_mut(item_name)
                        .unwrap()
                        .push(local_clause);
                }
            }
            self.trait_clauses
                .entry(clause.trait_.trait_id)
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
            TraitRefKind::SelfId,
            PredicateOrigin::TraitSelf,
        )?;
        if let Some(clause) = clause {
            self.trait_clauses
                .entry(clause.trait_.trait_id)
                .or_default()
                .push(clause);
        }
        Ok(())
    }

    pub(crate) fn translate_trait_clause_aux(
        &mut self,
        hspan: &hax::Span,
        trait_pred: &hax::TraitPredicate,
        clause_id: TraitRefKind,
        origin: PredicateOrigin,
    ) -> Result<Option<NonLocalTraitClause>, Error> {
        // Note sure what this is about
        assert!(trait_pred.is_positive);
        let span = hspan.rust_span_data.unwrap().span();

        // We translate trait clauses for signatures, etc. so we do not erase the regions
        let erase_regions = false;

        let trait_ref = &trait_pred.trait_ref;
        let trait_id = self.register_trait_decl_id(span, DefId::from(&trait_ref.def_id));

        let (regions, types, const_generics) =
            self.translate_substs(span, erase_regions, None, &trait_ref.generic_args)?;
        // There are no trait refs
        let generics = GenericArgs::new(regions, types, const_generics, Default::default());

        let span = self.translate_span_from_hax(hspan.clone());

        Ok(Some(NonLocalTraitClause {
            clause_id,
            span: Some(span),
            origin,
            trait_: TraitDeclRef { trait_id, generics },
        }))
    }

    pub(crate) fn translate_predicate(
        &mut self,
        pred: &hax::Predicate,
        hspan: &hax::Span,
        origin: PredicateOrigin,
        location: &PredicateLocation,
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
                        .translate_trait_clause(hspan, trait_pred, origin, location)?
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
    ) -> Result<Vector<TraitClauseId, TraitRef>, Error> {
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
                    Ok(Some(TraitRef {
                        kind: TraitRefKind::Unknown(err.msg),
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
                let trait_id = self.register_trait_impl_id(span, def_id);
                let generics = self.translate_substs_and_trait_refs(
                    span,
                    erase_regions,
                    None,
                    generics,
                    nested,
                )?;
                TraitRef {
                    kind: TraitRefKind::TraitImpl(trait_id, generics),
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
                let trait_decl_id = self.register_trait_decl_id(span, def_id);

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
                    ImplExprAtom::SelfImpl { .. } => TraitRefKind::SelfId,
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
                            trait_id = TraitRefKind::ItemClause(
                                Box::new(trait_id),
                                current_trait_decl_id,
                                TraitItemName(item.name.clone()),
                                TraitClauseId::new(*index),
                            );
                            current_trait_decl_id = self.register_trait_decl_id(
                                span,
                                DefId::from(&predicate.value.trait_ref.def_id),
                            );
                        }
                        Parent {
                            predicate,
                            index,
                            predicate_id: _,
                        } => {
                            trait_id = TraitRefKind::ParentClause(
                                Box::new(trait_id),
                                current_trait_decl_id,
                                TraitClauseId::new(*index),
                            );
                            current_trait_decl_id = self.register_trait_decl_id(
                                span,
                                DefId::from(&predicate.value.trait_ref.def_id),
                            );
                        }
                    }
                }

                // Ignore the arguments: we forbid using universal quantifiers
                // on the trait clauses for now.
                TraitRef {
                    kind: trait_id,
                    trait_decl_ref,
                }
            }
            ImplExprAtom::Dyn => TraitRef {
                kind: TraitRefKind::Dyn(trait_decl_ref.clone()),
                trait_decl_ref,
            },
            ImplExprAtom::Builtin { .. } => TraitRef {
                kind: TraitRefKind::BuiltinOrAuto(trait_decl_ref.clone()),
                trait_decl_ref,
            },
            ImplExprAtom::Todo(msg) => {
                let error = format!("Error during trait resolution: {}", msg);
                self.span_err(span, &error);
                if !self.t_ctx.continue_on_failure() {
                    panic!("{}", error)
                } else {
                    TraitRef {
                        kind: TraitRefKind::Unknown(msg.clone()),
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
        trace!(
            "Matching trait clauses:\n- trait_id: {:?}\n- generics: {:?}\n- clause.trait_: {:?}",
            fmt_ctx.format_object(trait_id),
            generics.fmt_with_ctx(&fmt_ctx),
            clause.trait_.fmt_with_ctx(&fmt_ctx)
        );
        assert_eq!(clause.trait_.trait_id, trait_id);
        // Ignoring the regions for now
        let tgt_types = &generics.types;
        let tgt_const_generics = &generics.const_generics;

        let src_types = &clause.trait_.generics.types;
        let src_const_generics = &clause.trait_.generics.const_generics;

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
    ) -> TraitRefKind {
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
            TraitRefKind::Unknown(format!(
                "Could not find a clause for parameter: {} (available clauses: {}) (context: {:?})",
                trait_ref,
                clauses.join("; "),
                self.def_id
            ))
        }
    }
}
