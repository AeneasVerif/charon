use super::translate_ctx::*;
use super::translate_traits::PredicateLocation;
use charon_lib::ast::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use hax_frontend_exporter as hax;

impl<'tcx, 'ctx> BodyTransCtx<'tcx, 'ctx> {
    /// This function should be called **after** we translated the generics (type parameters,
    /// regions...).
    pub(crate) fn register_predicates(
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
                self.register_predicate(pred, span, origin.clone(), location)?;
            }
        }
        for (pred, span) in &preds.predicates {
            if !matches!(
                pred.kind.value,
                hax::PredicateKind::Clause(hax::ClauseKind::Trait(_))
            ) {
                self.register_predicate(pred, span, origin.clone(), location)?;
            }
        }
        Ok(())
    }

    pub(crate) fn translate_trait_decl_ref(
        &mut self,
        span: Span,
        bound_trait_ref: &hax::Binder<hax::TraitRef>,
    ) -> Result<PolyTraitDeclRef, Error> {
        self.translate_region_binder(span, bound_trait_ref, move |ctx, trait_ref| {
            let trait_id = ctx.register_trait_decl_id(span, &trait_ref.def_id);
            let generics =
                ctx.translate_generic_args(span, None, &trait_ref.generic_args, &[], None)?;
            Ok(TraitDeclRef { trait_id, generics })
        })
    }

    pub(crate) fn translate_trait_predicate(
        &mut self,
        span: Span,
        trait_pred: &hax::TraitPredicate,
    ) -> Result<TraitDeclRef, Error> {
        // we don't handle negative trait predicates.
        assert!(trait_pred.is_positive);
        self.translate_trait_ref(span, &trait_pred.trait_ref)
    }

    pub(crate) fn translate_trait_ref(
        &mut self,
        span: Span,
        trait_ref: &hax::TraitRef,
    ) -> Result<TraitDeclRef, Error> {
        let trait_id = self.register_trait_decl_id(span, &trait_ref.def_id);
        // For now a trait has no required bounds, so we pass an empty list.
        let generics =
            self.translate_generic_args(span, None, &trait_ref.generic_args, &[], None)?;
        Ok(TraitDeclRef { trait_id, generics })
    }

    pub(crate) fn register_predicate(
        &mut self,
        pred: &hax::Predicate,
        hspan: &hax::Span,
        origin: PredicateOrigin,
        location: &PredicateLocation,
    ) -> Result<(), Error> {
        use hax::{ClauseKind, PredicateKind};
        trace!("{:?}", pred);
        let span = self.translate_span_from_hax(hspan);
        match pred.kind.hax_skip_binder_ref() {
            PredicateKind::Clause(kind) => {
                match kind {
                    ClauseKind::Trait(trait_pred) => {
                        let pred = self.translate_region_binder(span, &pred.kind, |ctx, _| {
                            ctx.translate_trait_predicate(span, trait_pred)
                        })?;
                        let location = match location {
                            PredicateLocation::Base => {
                                &mut self.top_level_generics_mut().trait_clauses
                            }
                            PredicateLocation::Parent => &mut self.parent_trait_clauses,
                            PredicateLocation::Item(item_name) => self
                                .item_trait_clauses
                                .entry(item_name.clone())
                                .or_default(),
                        };
                        location.push_with(|clause_id| TraitClause {
                            clause_id,
                            origin,
                            span: Some(span),
                            trait_: pred,
                        });
                    }
                    ClauseKind::RegionOutlives(p) => {
                        let pred = self.translate_region_binder(span, &pred.kind, |ctx, _| {
                            let r0 = ctx.translate_region(span, &p.lhs)?;
                            let r1 = ctx.translate_region(span, &p.rhs)?;
                            Ok(OutlivesPred(r0, r1))
                        })?;
                        self.top_level_generics_mut().regions_outlive.push(pred);
                    }
                    ClauseKind::TypeOutlives(p) => {
                        let pred = self.translate_region_binder(span, &pred.kind, |ctx, _| {
                            let ty = ctx.translate_ty(span, &p.lhs)?;
                            let r = ctx.translate_region(span, &p.rhs)?;
                            Ok(OutlivesPred(ty, r))
                        })?;
                        self.top_level_generics_mut().types_outlive.push(pred);
                    }
                    ClauseKind::Projection(p) => {
                        // This is used to express constraints over associated types.
                        // For instance:
                        // ```
                        // T : Foo<S = String>
                        //         ^^^^^^^^^^
                        // ```
                        let pred = self.translate_region_binder(span, &pred.kind, |ctx, _| {
                            let trait_ref = ctx.translate_trait_impl_expr(span, &p.impl_expr)?;
                            let ty = ctx.translate_ty(span, &p.ty)?;
                            let type_name = TraitItemName(p.assoc_item.name.clone());
                            Ok(TraitTypeConstraint {
                                trait_ref,
                                type_name,
                                ty,
                            })
                        })?;
                        self.top_level_generics_mut()
                            .trait_type_constraints
                            .push(pred);
                    }
                    ClauseKind::ConstArgHasType(..) => {
                        // I don't really understand that one. Why don't they put
                        // the type information in the const generic parameters
                        // directly? For now we just ignore it.
                    }
                    ClauseKind::WellFormed(_) => {
                        error_or_panic!(
                            self,
                            span,
                            format!("Well-formedness clauses are unsupported")
                        )
                    }
                    ClauseKind::ConstEvaluatable(_) => {
                        error_or_panic!(self, span, format!("Unsupported clause: {:?}", kind))
                    }
                }
            }
            PredicateKind::AliasRelate(..)
            | PredicateKind::Ambiguous
            | PredicateKind::Coerce(_)
            | PredicateKind::ConstEquate(_, _)
            | PredicateKind::DynCompatible(_)
            | PredicateKind::NormalizesTo(_)
            | PredicateKind::Subtype(_) => {
                error_or_panic!(self, span, format!("Unsupported predicate: {:?}", pred))
            }
        }
        Ok(())
    }

    pub(crate) fn translate_trait_impl_exprs(
        &mut self,
        span: Span,
        impl_sources: &[hax::ImplExpr],
    ) -> Result<Vector<TraitClauseId, TraitRef>, Error> {
        impl_sources
            .iter()
            .map(|x| self.translate_trait_impl_expr(span, x))
            .try_collect()
    }

    #[tracing::instrument(skip(self, span, impl_expr))]
    pub(crate) fn translate_trait_impl_expr(
        &mut self,
        span: Span,
        impl_expr: &hax::ImplExpr,
    ) -> Result<TraitRef, Error> {
        let trait_decl_ref = self.translate_trait_decl_ref(span, &impl_expr.r#trait)?;

        match self.translate_trait_impl_expr_aux(span, impl_expr, trait_decl_ref.clone()) {
            Ok(res) => Ok(res),
            Err(err) => {
                if !self.t_ctx.continue_on_failure() {
                    panic!("Error during trait resolution: {}", err.msg)
                } else {
                    let msg = format!("Error during trait resolution: {}", &err.msg);
                    self.span_err(span, &msg);
                    Ok(TraitRef {
                        kind: TraitRefKind::Unknown(err.msg),
                        trait_decl_ref,
                    })
                }
            }
        }
    }

    pub(crate) fn translate_trait_impl_expr_aux(
        &mut self,
        span: Span,
        impl_source: &hax::ImplExpr,
        trait_decl_ref: PolyTraitDeclRef,
    ) -> Result<TraitRef, Error> {
        trace!("impl_expr: {:#?}", impl_source);
        use hax::ImplExprAtom;

        let nested = &impl_source.args;
        let trait_ref = match &impl_source.r#impl {
            ImplExprAtom::Concrete {
                id: impl_def_id,
                generics,
            } => {
                let impl_id = self.register_trait_impl_id(span, impl_def_id);
                let generics = self.translate_generic_args(span, None, generics, nested, None)?;
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
                r#trait: trait_ref,
                path,
                ..
            } => {
                assert!(nested.is_empty());
                trace!(
                    "impl source (self or clause): param:\n- trait_ref: {:?}\n- path: {:?}",
                    trait_ref,
                    path,
                );
                // If we are refering to a trait clause, we need to find the
                // relevant one.
                let mut trait_id = match &impl_source.r#impl {
                    ImplExprAtom::SelfImpl { .. } => TraitRefKind::SelfId,
                    ImplExprAtom::LocalBound { index, .. } => {
                        let var = self.lookup_clause_var(*index).unwrap();
                        TraitRefKind::Clause(var)
                    }
                    _ => unreachable!(),
                };

                let mut current_trait_decl_id =
                    self.register_trait_decl_id(span, &trait_ref.hax_skip_binder_ref().def_id);

                // Apply the path
                for path_elem in path {
                    use hax::ImplExprPathChunk::*;
                    match path_elem {
                        AssocItem {
                            item,
                            generic_args,
                            predicate,
                            index,
                            ..
                        } => {
                            if !generic_args.is_empty() {
                                error_or_panic!(
                                    self,
                                    span,
                                    format!(
                                        "Found unsupported GAT `{}` when resolving trait `{}`",
                                        item.name,
                                        trait_decl_ref.fmt_with_ctx(&self.into_fmt())
                                    )
                                )
                            }
                            trait_id = TraitRefKind::ItemClause(
                                Box::new(trait_id),
                                current_trait_decl_id,
                                TraitItemName(item.name.clone()),
                                TraitClauseId::new(*index),
                            );
                            current_trait_decl_id = self.register_trait_decl_id(
                                span,
                                &predicate.hax_skip_binder_ref().trait_ref.def_id,
                            );
                        }
                        Parent {
                            predicate, index, ..
                        } => {
                            trait_id = TraitRefKind::ParentClause(
                                Box::new(trait_id),
                                current_trait_decl_id,
                                TraitClauseId::new(*index),
                            );
                            current_trait_decl_id = self.register_trait_decl_id(
                                span,
                                &predicate.hax_skip_binder_ref().trait_ref.def_id,
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
            ImplExprAtom::Error(msg) => {
                let trait_ref = TraitRef {
                    kind: TraitRefKind::Unknown(msg.clone()),
                    trait_decl_ref,
                };
                if self.error_on_impl_expr_error {
                    let error = format!("Error during trait resolution: {}", msg);
                    self.span_err(span, &error);
                    if !self.t_ctx.continue_on_failure() {
                        panic!("{}", error)
                    }
                }
                trait_ref
            }
        };
        Ok(trait_ref)
    }
}
