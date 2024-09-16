use super::translate_ctx::*;
use super::translate_traits::PredicateLocation;
use charon_lib::common::*;
use charon_lib::formatter::AstFormatter;
use charon_lib::gast::*;
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::types::*;
use hax_frontend_exporter as hax;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters};
use rustc_span::def_id::DefId;

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
    pub hax_trait_ref: hax::TraitRef,
    pub trait_ref_kind: TraitRefKind,
}

impl NonLocalTraitClause {
    fn matches(&self, hax_trait_ref: &hax::TraitRef) -> bool {
        // We ignore regions.
        let skip_lifetimes = |arg: &&hax::GenericArg| match arg {
            hax::GenericArg::Lifetime(_) => false,
            _ => true,
        };
        hax_trait_ref
            .generic_args
            .iter()
            .filter(skip_lifetimes)
            .eq(self
                .hax_trait_ref
                .generic_args
                .iter()
                .filter(skip_lifetimes))
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for NonLocalTraitClause {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let clause_id = self.trait_ref_kind.fmt_with_ctx(ctx);
        let generics_ = &self.hax_trait_ref;
        format!("[{clause_id}]: {generics_:?}")
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
                        Predicate::TypeOutlives(p) => self.generic_params.types_outlive.push(p),
                        Predicate::RegionOutlives(p) => self.generic_params.regions_outlive.push(p),
                        Predicate::TraitType(p) => {
                            self.generic_params.trait_type_constraints.push(p)
                        }
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
        let trait_id = self.register_trait_decl_id(span, &trait_ref.def_id);
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
        let span = self.translate_span_from_hax(hspan.clone());

        let trait_decl_ref = self.translate_trait_predicate(hspan, trait_pred)?;
        let vec = match location {
            PredicateLocation::Base => &mut self.generic_params.trait_clauses,
            PredicateLocation::Parent(..) => &mut self.parent_trait_clauses,
            PredicateLocation::Item(.., item_name) => self
                .item_trait_clauses
                .entry(item_name.clone())
                .or_default(),
        };
        let clause_id = vec.push_with(|clause_id| TraitClause {
            clause_id,
            origin,
            span: Some(span),
            trait_: trait_decl_ref,
        });

        let trait_ref_kind = match location {
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
        let def_id = DefId::from(&trait_pred.trait_ref.def_id);
        self.trait_clauses_map
            .entry(OrdRustId::TraitDecl(def_id))
            .or_default()
            .push(NonLocalTraitClause {
                hax_trait_ref: trait_pred.trait_ref.clone(),
                trait_ref_kind,
            });

        Ok(Some(clause_id))
    }

    /// Returns an [Option] because we may filter clauses about builtin or
    /// auto traits like [core::marker::Sized] and [core::marker::Sync].
    pub(crate) fn translate_self_trait_clause(
        &mut self,
        span: &hax::Span,
        trait_pred: &hax::TraitPredicate,
    ) -> Result<(), Error> {
        // Save the self clause (and its parent/item clauses)
        let _ = self.translate_trait_predicate(span, &trait_pred)?;
        let clause = NonLocalTraitClause {
            hax_trait_ref: trait_pred.trait_ref.clone(),
            trait_ref_kind: TraitRefKind::SelfId,
        };
        let def_id = DefId::from(&trait_pred.trait_ref.def_id);
        self.trait_clauses_map
            .entry(OrdRustId::TraitDecl(def_id))
            .or_default()
            .push(clause);
        Ok(())
    }

    pub(crate) fn translate_trait_predicate(
        &mut self,
        hspan: &hax::Span,
        trait_pred: &hax::TraitPredicate,
    ) -> Result<TraitDeclRef, Error> {
        // Note sure what this is about
        assert!(trait_pred.is_positive);
        let span = hspan.rust_span_data.unwrap().span();

        // We translate trait clauses for signatures, etc. so we do not erase the regions
        let erase_regions = false;

        let trait_ref = &trait_pred.trait_ref;
        let trait_id = self.register_trait_decl_id(span, &trait_ref.def_id);

        let (regions, types, const_generics) =
            self.translate_substs(span, erase_regions, None, &trait_ref.generic_args)?;
        // There are no trait refs
        let generics = GenericArgs::new(regions, types, const_generics, Default::default());

        Ok(TraitDeclRef { trait_id, generics })
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
    #[tracing::instrument(skip(self, span, erase_regions))]
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
                let impl_id = self.register_trait_impl_id(span, impl_def_id);
                let generics = self.translate_substs_and_trait_refs(
                    span,
                    erase_regions,
                    None,
                    generics,
                    nested,
                )?;
                TraitRef {
                    kind: TraitRefKind::TraitImpl(impl_id, generics),
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
                assert!(nested.is_empty());
                trace!(
                    "impl source (self or clause): param:\n- trait_ref: {:?}\n- path: {:?}",
                    trait_ref,
                    path,
                );
                assert!(trait_ref.bound_vars.is_empty());
                let trait_ref = &trait_ref.value;

                // If we are refering to a trait clause, we need to find the
                // relevant one.
                let mut trait_id = match &impl_source.r#impl {
                    ImplExprAtom::SelfImpl { .. } => TraitRefKind::SelfId,
                    ImplExprAtom::LocalBound { .. } => self.find_trait_clause_for_param(trait_ref),
                    _ => unreachable!(),
                };

                let mut current_trait_decl_id =
                    self.register_trait_decl_id(span, &trait_ref.def_id);

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
                            current_trait_decl_id = self
                                .register_trait_decl_id(span, &predicate.value.trait_ref.def_id);
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
                            current_trait_decl_id = self
                                .register_trait_decl_id(span, &predicate.value.trait_ref.def_id);
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

    /// Find the trait instance fullfilling a trait obligation.
    /// TODO: having to do this is very annoying. Isn't there a better way?
    #[tracing::instrument(skip(self))]
    pub(crate) fn find_trait_clause_for_param(
        &mut self,
        hax_trait_ref: &hax::TraitRef,
    ) -> TraitRefKind {
        trace!(
            "Inside context of: {:?}\nSpan: {:?}",
            self.def_id,
            self.t_ctx.tcx.def_ident_span(self.def_id)
        );

        // Simply explore the trait clauses
        let def_id = DefId::from(&hax_trait_ref.def_id);
        if let Some(clauses_for_this_trait) =
            self.trait_clauses_map.get(&OrdRustId::TraitDecl(def_id))
        {
            for trait_clause in clauses_for_this_trait {
                if trait_clause.matches(hax_trait_ref) {
                    return trait_clause.trait_ref_kind.clone();
                }
            }
        };

        // Try solving it again later, when more clauses are registered.
        let id = self.unsolved_traits.push(hax_trait_ref.clone());
        TraitRefKind::Unsolved(id)
    }
}
