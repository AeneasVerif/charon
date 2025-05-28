use super::translate_ctx::*;
use super::translate_traits::PredicateLocation;
use charon_lib::ast::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use hax_frontend_exporter as hax;

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
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
        for (clause, span) in &preds.predicates {
            if matches!(clause.kind.value, hax::ClauseKind::Trait(_)) {
                self.register_predicate(clause, span, origin.clone(), location)?;
            }
        }
        for (clause, span) in &preds.predicates {
            if !matches!(clause.kind.value, hax::ClauseKind::Trait(_)) {
                self.register_predicate(clause, span, origin.clone(), location)?;
            }
        }
        Ok(())
    }

    pub(crate) fn translate_poly_trait_ref(
        &mut self,
        span: Span,
        bound_trait_ref: &hax::Binder<hax::TraitRef>,
    ) -> Result<PolyTraitDeclRef, Error> {
        self.translate_region_binder(span, bound_trait_ref, move |ctx, trait_ref| {
            ctx.translate_trait_ref(span, trait_ref)
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
        let generics = self.translate_generic_args(
            span,
            &trait_ref.generic_args,
            &[],
            None,
            GenericsSource::item(trait_id),
        )?;
        Ok(TraitDeclRef {
            trait_id,
            generics: Box::new(generics),
        })
    }

    pub(crate) fn register_predicate(
        &mut self,
        clause: &hax::Clause,
        hspan: &hax::Span,
        origin: PredicateOrigin,
        location: &PredicateLocation,
    ) -> Result<(), Error> {
        use hax::ClauseKind;
        trace!("{:?}", clause);
        let span = self.translate_span_from_hax(hspan);
        match clause.kind.hax_skip_binder_ref() {
            ClauseKind::Trait(trait_pred) => {
                let pred = self.translate_region_binder(span, &clause.kind, |ctx, _| {
                    ctx.translate_trait_predicate(span, trait_pred)
                })?;
                let location = match location {
                    PredicateLocation::Base => &mut self.innermost_generics_mut().trait_clauses,
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
                let pred = self.translate_region_binder(span, &clause.kind, |ctx, _| {
                    let r0 = ctx.translate_region(span, &p.lhs)?;
                    let r1 = ctx.translate_region(span, &p.rhs)?;
                    Ok(OutlivesPred(r0, r1))
                })?;
                self.innermost_generics_mut().regions_outlive.push(pred);
            }
            ClauseKind::TypeOutlives(p) => {
                let pred = self.translate_region_binder(span, &clause.kind, |ctx, _| {
                    let ty = ctx.translate_ty(span, &p.lhs)?;
                    let r = ctx.translate_region(span, &p.rhs)?;
                    Ok(OutlivesPred(ty, r))
                })?;
                self.innermost_generics_mut().types_outlive.push(pred);
            }
            ClauseKind::Projection(p) => {
                // This is used to express constraints over associated types.
                // For instance:
                // ```
                // T : Foo<S = String>
                //         ^^^^^^^^^^
                // ```
                let pred = self.translate_region_binder(span, &clause.kind, |ctx, _| {
                    let trait_ref = ctx.translate_trait_impl_expr(span, &p.impl_expr)?;
                    let ty = ctx.translate_ty(span, &p.ty)?;
                    let type_name = TraitItemName(p.assoc_item.name.clone());
                    Ok(TraitTypeConstraint {
                        trait_ref,
                        type_name,
                        ty,
                    })
                })?;
                self.innermost_generics_mut()
                    .trait_type_constraints
                    .push(pred);
            }
            ClauseKind::ConstArgHasType(..) => {
                // I don't really understand that one. Why don't they put
                // the type information in the const generic parameters
                // directly? For now we just ignore it.
            }
            ClauseKind::WellFormed(_) => {
                raise_error!(self, span, "Well-formedness clauses are unsupported")
            }
            kind => {
                raise_error!(self, span, "Unsupported clause: {:?}", kind)
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
        let trait_decl_ref = self.translate_poly_trait_ref(span, &impl_expr.r#trait)?;

        match self.translate_trait_impl_expr_aux(span, impl_expr, trait_decl_ref.clone()) {
            Ok(res) => Ok(res),
            Err(err) => {
                register_error!(self, span, "Error during trait resolution: {}", &err.msg);
                Ok(TraitRef {
                    kind: TraitRefKind::Unknown(err.msg),
                    trait_decl_ref,
                })
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

        let trait_ref = match &impl_source.r#impl {
            ImplExprAtom::Concrete {
                id: impl_def_id,
                generics,
                impl_exprs,
            } => {
                let impl_id = self.register_trait_impl_id(span, impl_def_id);
                let generics = self.translate_generic_args(
                    span,
                    generics,
                    impl_exprs,
                    None,
                    GenericsSource::item(impl_id),
                )?;
                TraitRef {
                    kind: TraitRefKind::TraitImpl(impl_id, Box::new(generics)),
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
                        let var = self.lookup_clause_var(span, *index)?;
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
                                raise_error!(
                                    self,
                                    span,
                                    "Found unsupported GAT `{}` when resolving trait `{}`",
                                    item.name,
                                    trait_decl_ref.fmt_with_ctx(&self.into_fmt())
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
            ImplExprAtom::Builtin {
                impl_exprs,
                types,
                r#trait: builtin_trait,
            } => {
                use hax_frontend_exporter::DefPathItem;
                let closure_kind = builtin_trait
                    .hax_skip_binder_ref()
                    .def_id
                    .path
                    .last()
                    .and_then(|f| match &f.data {
                        DefPathItem::TypeNs(name) => name.as_ref(),
                        _ => None,
                    })
                    .and_then(|s| match s.as_str() {
                        "FnOnce" => Some(hax::ClosureKind::FnOnce),
                        "FnMut" => Some(hax::ClosureKind::FnMut),
                        "Fn" => Some(hax::ClosureKind::Fn),
                        _ => None,
                    });

                let is_closure = closure_kind.as_ref().is_some_and(|_| {
                    if let Some(hax::GenericArg::Type(closure_ty)) = impl_source
                        .r#trait
                        .hax_skip_binder_ref()
                        .generic_args
                        .first()
                    {
                        matches!(closure_ty.kind(), hax::TyKind::Closure(..))
                    } else {
                        false
                    }
                });

                if is_closure {
                    let binder =
                        self.translate_region_binder(span, &impl_source.r#trait, |ctx, tref| {
                            let Some(hax::GenericArg::Type(closure_ty)) = tref.generic_args.first()
                            else {
                                unreachable!();
                            };
                            let hax::TyKind::Closure(closure_id, closure_args) = closure_ty.kind()
                            else {
                                unreachable!();
                            };

                            let impl_id = ctx.register_closure_trait_impl_id(
                                span,
                                &closure_id,
                                &closure_kind.unwrap(),
                            );

                            let parent_args = ctx.translate_closure_generic_args(
                                span,
                                closure_args,
                                GenericsSource::item(impl_id),
                            )?;

                            Ok((impl_id, parent_args))
                        })?;
                    let (impl_id, parent_args) = binder.erase();
                    TraitRef {
                        kind: TraitRefKind::TraitImpl(impl_id, parent_args.into()),
                        trait_decl_ref,
                    }
                } else {
                    let parent_trait_refs = self.translate_trait_impl_exprs(span, &impl_exprs)?;
                    let types = types
                        .iter()
                        .map(|(def_id, ty)| {
                            let item_def = self.hax_def(def_id)?;
                            let ty = self.translate_ty(span, ty)?;
                            let hax::FullDefKind::AssocTy {
                                associated_item, ..
                            } = item_def.kind()
                            else {
                                unreachable!()
                            };
                            let name = TraitItemName(associated_item.name.clone());
                            Ok((name, ty))
                        })
                        .try_collect()?;
                    TraitRef {
                        kind: TraitRefKind::BuiltinOrAuto {
                            trait_decl_ref: trait_decl_ref.clone(),
                            parent_trait_refs,
                            types,
                        },
                        trait_decl_ref,
                    }
                }
            }
            ImplExprAtom::Error(msg) => {
                let trait_ref = TraitRef {
                    kind: TraitRefKind::Unknown(msg.clone()),
                    trait_decl_ref,
                };
                if self.error_on_impl_expr_error {
                    register_error!(self, span, "Error during trait resolution: {}", msg);
                }
                trait_ref
            }
        };
        Ok(trait_ref)
    }
}
