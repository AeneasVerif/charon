//! Trait resolution: given a trait reference, we track which local clause caused it to be true.

use crate::*;
use itertools::{Either, Itertools};
use std::collections::{HashMap, hash_map::Entry};

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::traits::CodegenObligationError;
use rustc_middle::ty::{self, *};
use rustc_trait_selection::traits::ImplSource;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct ItemClause<'tcx> {
    id: ItemPredicateId,
    clause: PolyTraitRef<'tcx>,
}

/// Returns the predicate to resolve as `Self`, if that makes sense in the current item.
/// Currently this predicate is only used inside trait declarations and their asosciated types.
fn initial_self_pred<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_span::def_id::DefId,
) -> Option<PolyTraitRef<'tcx>> {
    use DefKind::*;
    let trait_def_id = match tcx.def_kind(def_id) {
        Trait | TraitAlias => def_id,
        // Associated types can refer to the implicit `Self` clause. For methods and associated
        // consts we pass an explicit `Self: Trait` clause to make the corresponding item
        // reuseable.
        AssocTy => tcx.parent(def_id),
        _ => return None,
    };
    let self_pred = self_predicate(tcx, trait_def_id).upcast(tcx);
    Some(self_pred)
}

#[tracing::instrument(level = "trace", skip(tcx))]
fn parents_trait_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    self_trait_ref: PolyTraitRef<'tcx>,
    options: &BoundsOptions,
) -> Vec<PolyTraitRef<'tcx>> {
    ItemPredicates::implied(tcx, self_trait_ref.def_id(), options)
        .iter()
        // Substitute with the `self` args so that the clause makes sense in the
        // outside context.
        .map(|pred| pred.clause.instantiate_supertrait(tcx, self_trait_ref))
        .filter_map(|pred| pred.as_trait_clause())
        .map(|pred| pred.to_poly_trait_ref())
        .collect()
}

/// A candidate projects `self` along a path reaching some predicate. A candidate is
/// selected when its predicate is the one expected, aka `target`.
#[derive(Debug, Clone)]
struct Candidate<'tcx> {
    path: Path<'tcx>,
    pred: PolyTraitRef<'tcx>,
    origin: ItemClause<'tcx>,
}

impl<'tcx> Candidate<'tcx> {
    fn into_impl_expr(self, tcx: TyCtxt<'tcx>, implicit_self_clause: bool) -> ImplExprAtom<'tcx> {
        let path = self.path;
        let r#trait = self.origin.clause;
        match self.origin.id {
            ItemPredicateId::TraitSelf if implicit_self_clause => {
                ImplExprAtom::SelfImpl { r#trait, path }
            }
            _ => ImplExprAtom::LocalBound {
                predicate: self.origin.clause.upcast(tcx),
                id: self.origin.id,
                r#trait,
                path,
            },
        }
    }
}

/// Stores a set of predicates along with where they came from.
#[derive(Clone)]
pub struct PredicateSearcher<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    /// Local clauses available in the current context.
    candidates: HashMap<PolyTraitRef<'tcx>, Candidate<'tcx>>,
    /// Resolution options.
    pub(crate) options: BoundsOptions,
    /// Whether we're in a trait declaration context where an implicit `Self: Trait` clause is
    /// accessible.
    implicit_self_clause: bool,
}

impl<'tcx> PredicateSearcher<'tcx> {
    /// Initialize the elaborator with the predicates accessible within this item.
    pub fn new_for_owner(tcx: TyCtxt<'tcx>, owner_id: DefId, options: &BoundsOptions) -> Self {
        let initial_self_pred = initial_self_pred(tcx, owner_id);
        let mut out = Self {
            tcx,
            typing_env: TypingEnv {
                param_env: tcx.param_env(owner_id),
                typing_mode: TypingMode::PostAnalysis,
            },
            candidates: Default::default(),
            options: options.clone(),
            implicit_self_clause: initial_self_pred.is_some(),
        };
        out.insert_predicates(initial_self_pred.map(|clause| ItemClause {
            id: ItemPredicateId::TraitSelf,
            clause,
        }));
        out.insert_bound_predicates(
            ItemPredicates::required_recursively(tcx, owner_id, options).predicates,
        );
        out
    }

    /// Insert the bound clauses in the search context. Prefer inserting them all at once as this
    /// will give priority to shorter resolution paths. Bound clauses are numbered from `0` in
    /// insertion order.
    pub fn insert_bound_predicates(
        &mut self,
        preds: impl IntoIterator<Item = ItemPredicate<'tcx>>,
    ) {
        self.insert_predicates(preds.into_iter().filter_map(|pred| {
            pred.clause.as_trait_clause().map(|clause| ItemClause {
                id: pred.id,
                clause: clause.to_poly_trait_ref(),
            })
        }));
    }

    /// Override the param env; we use this when resolving `dyn` predicates to add more clauses to
    /// the scope.
    pub fn set_param_env(&mut self, param_env: ParamEnv<'tcx>) {
        self.typing_env.param_env = param_env;
    }

    /// Insert annotated predicates in the search context. Prefer inserting them all at once as
    /// this will give priority to shorter resolution paths.
    fn insert_predicates(&mut self, preds: impl IntoIterator<Item = ItemClause<'tcx>>) {
        self.insert_candidates(preds.into_iter().map(|clause| Candidate {
            path: vec![],
            pred: clause.clause,
            origin: clause,
        }))
    }

    /// Insert new candidates and all their parent predicates. This deduplicates predicates
    /// to avoid divergence.
    fn insert_candidates(&mut self, candidates: impl IntoIterator<Item = Candidate<'tcx>>) {
        let tcx = self.tcx;
        // Filter out duplicated candidates.
        let mut new_candidates = Vec::new();
        for mut candidate in candidates {
            // Normalize and erase all lifetimes.
            candidate.pred = normalize_bound_val(tcx, self.typing_env, candidate.pred);
            if let Entry::Vacant(entry) = self.candidates.entry(candidate.pred) {
                entry.insert(candidate.clone());
                new_candidates.push(candidate);
            }
        }
        if !new_candidates.is_empty() {
            // Insert the parents all at once.
            self.insert_candidate_parents(new_candidates);
        }
    }

    /// Add the parents of these candidates. This is a separate function to avoid
    /// polymorphic recursion due to the closures capturing the type parameters of this
    /// function.
    fn insert_candidate_parents(&mut self, new_candidates: Vec<Candidate<'tcx>>) {
        let tcx = self.tcx;
        // Then recursively add their parents. This way ensures a breadth-first order,
        // which means we select the shortest path when looking up predicates.
        let options = self.options.clone();
        self.insert_candidates(new_candidates.into_iter().flat_map(|candidate| {
            parents_trait_predicates(tcx, candidate.pred, &options)
                .into_iter()
                .enumerate()
                .map(move |(index, parent_pred)| {
                    let mut parent_candidate = Candidate {
                        pred: parent_pred,
                        path: candidate.path.clone(),
                        origin: candidate.origin,
                    };
                    parent_candidate.path.push(PathChunk::Parent {
                        predicate: parent_pred,
                        index,
                    });
                    parent_candidate
                })
        }));
    }

    /// If the type is a trait associated type, we add any relevant bounds to our context.
    fn add_associated_type_refs(&mut self, ty: Binder<'tcx, Ty<'tcx>>) {
        let tcx = self.tcx;
        // Note: We skip a binder but rebind it just after.
        let TyKind::Alias(AliasTyKind::Projection, alias_ty) = ty.skip_binder().kind() else {
            return;
        };
        let trait_ref = ty.rebind(alias_ty.trait_ref(tcx)).upcast(tcx);

        // The predicate we're looking for is is `<T as Trait>::Type: OtherTrait`. We look up `T as
        // Trait` in the current context and add all the bounds on `Trait::Type` to our context.
        let Some(trait_candidate) = self.resolve_local(trait_ref) else {
            return;
        };

        // The bounds that hold on the associated type.
        let item_bounds = ItemPredicates::implied(tcx, alias_ty.def_id, &self.options);
        let item_bounds = item_bounds
            .iter_trait_clauses()
            // Substitute the item generics
            .map(|(_, tref)| EarlyBinder::bind(tref).instantiate(tcx, alias_ty.args))
            .enumerate();

        // Add all the bounds on the corresponding associated item.
        self.insert_candidates(item_bounds.map(|(index, pred)| {
            let mut candidate = Candidate {
                path: trait_candidate.path.clone(),
                pred,
                origin: trait_candidate.origin,
            };
            candidate.path.push(PathChunk::AssocItem {
                item: tcx.associated_item(alias_ty.def_id),
                generic_args: alias_ty.args,
                predicate: pred,
                index,
            });
            candidate
        }));
    }

    /// Resolve a local clause by looking it up in this set. If the predicate applies to an
    /// associated type, we add the relevant implied associated type bounds to the set as well.
    fn resolve_local(&mut self, target: PolyTraitRef<'tcx>) -> Option<Candidate<'tcx>> {
        tracing::trace!("Looking for {target:?}");

        // Look up the predicate
        let ret = self.candidates.get(&target).cloned();
        if ret.is_some() {
            return ret;
        }

        // Add clauses related to associated type in the `Self` type of the predicate.
        self.add_associated_type_refs(target.self_ty());

        let ret = self.candidates.get(&target).cloned();
        if ret.is_none() {
            tracing::trace!(
                "Couldn't find {target:?} in: [\n{}]",
                self.candidates
                    .values()
                    .map(|c| format!("  - {:?}\n", c.pred))
                    .join("")
            );
        }
        ret
    }

    /// Resolve the given trait reference in the local context.
    #[tracing::instrument(level = "trace", skip(self))]
    pub fn resolve(&mut self, tref: &PolyTraitRef<'tcx>) -> ImplExpr<'tcx> {
        use rustc_trait_selection::traits::{
            BuiltinImplSource, ImplSource, ImplSourceUserDefinedData,
        };
        let tcx = self.tcx;
        let destruct_trait = tcx.lang_items().destruct_trait().unwrap();

        let erased_tref = normalize_bound_val(self.tcx, self.typing_env, *tref);
        let trait_def_id = erased_tref.skip_binder().def_id;

        let error = |msg: String| ImplExpr {
            r#impl: ImplExprAtom::Error(msg),
            r#trait: *tref,
        };

        let impl_source = shallow_resolve_trait_ref(tcx, self.typing_env.param_env, erased_tref);
        let impl_source = match impl_source {
            Ok(impl_source) => impl_source,
            Err(e) => {
                return error(format!(
                    "Could not find a clause for `{tref:?}` \
                    in the current context: `{e:?}`"
                ));
            }
        };
        let atom = match impl_source {
            ImplSource::UserDefined(ImplSourceUserDefinedData {
                impl_def_id,
                args: generics,
                ..
            }) => ImplExprAtom::Concrete {
                def_id: impl_def_id,
                generics,
            },
            ImplSource::Param(_) => match self.resolve_local(erased_tref.upcast(self.tcx)) {
                Some(candidate) => candidate.into_impl_expr(tcx, self.implicit_self_clause),
                None => {
                    let msg =
                        format!("Could not find a clause for `{tref:?}` in the item parameters");
                    return error(msg);
                }
            },
            ImplSource::Builtin(BuiltinImplSource::Object { .. }, _) => ImplExprAtom::Dyn,
            ImplSource::Builtin(_, _) => {
                // Resolve the predicates implied by the trait.
                // If we wanted to not skip this binder, we'd have to instantiate the bound
                // regions, solve, then wrap the result in a binder. And track higher-kinded
                // clauses better all over.
                let impl_exprs = self
                    .resolve_item_implied_predicates(trait_def_id, erased_tref.skip_binder().args);
                let types = tcx
                    .associated_items(trait_def_id)
                    .in_definition_order()
                    .filter(|assoc| matches!(assoc.kind, AssocKind::Type { .. }))
                    .filter_map(|assoc| {
                        let ty =
                            Ty::new_projection(tcx, assoc.def_id, erased_tref.skip_binder().args);
                        let ty = crate::erase_and_norm(tcx, self.typing_env, ty);
                        if let TyKind::Alias(_, alias_ty) = ty.kind()
                            && alias_ty.def_id == assoc.def_id
                        {
                            // Couldn't normalize the type to anything different than itself;
                            // this must be a built-in associated type such as
                            // `DiscriminantKind::Discriminant`.
                            // We can't return the unnormalized associated type as that would
                            // make the trait ref contain itself, which would make hax's
                            // `sinto` infrastructure loop. That's ok because we can't provide
                            // a value for this type other than the associate type alias
                            // itself.
                            return None;
                        }
                        let impl_exprs = self.resolve_item_implied_predicates(
                            assoc.def_id,
                            erased_tref.skip_binder().args,
                        );
                        Some((assoc.def_id, ty, impl_exprs))
                    })
                    .collect();

                let trait_data = if erased_tref.skip_binder().def_id == destruct_trait {
                    let ty = erased_tref.skip_binder().args[0].as_type().unwrap();
                    // Source of truth are `ty::needs_drop_components` and `tcx.needs_drop_raw`.
                    let destruct_data = match ty.kind() {
                        // TODO: Does `UnsafeBinder` drop its contents?
                        ty::Bool
                        | ty::Char
                        | ty::Int(..)
                        | ty::Uint(..)
                        | ty::Float(..)
                        | ty::Foreign(..)
                        | ty::Str
                        | ty::RawPtr(..)
                        | ty::Ref(..)
                        | ty::FnDef(..)
                        | ty::FnPtr(..)
                        | ty::UnsafeBinder(..)
                        | ty::Never => Either::Left(DestructData::Noop),
                        ty::Tuple(tys) if tys.is_empty() => Either::Left(DestructData::Noop),
                        ty::Array(..)
                        | ty::Pat(..)
                        | ty::Slice(..)
                        | ty::Tuple(..)
                        | ty::Adt(..)
                        | ty::Closure(..)
                        | ty::Coroutine(..)
                        | ty::CoroutineClosure(..)
                        | ty::CoroutineWitness(..) => Either::Left(DestructData::Glue { ty }),
                        // Every `dyn` has a `drop_in_place` in its vtable, ergo we pretend that every
                        // `dyn` has `Destruct` in its list of traits.
                        ty::Dynamic(..) => Either::Right(ImplExprAtom::Dyn),
                        ty::Param(..) | ty::Alias(..) | ty::Bound(..) => {
                            if self.options.add_destruct_bounds {
                                // We've added `Destruct` impls on everything, we should be able to resolve
                                // it.
                                match self.resolve_local(erased_tref.upcast(self.tcx)) {
                                    Some(candidate) => Either::Right(
                                        candidate.into_impl_expr(tcx, self.implicit_self_clause),
                                    ),
                                    None => {
                                        let msg = format!(
                                            "Cannot find virtual `Destruct` clause: `{tref:?}`"
                                        );
                                        return error(msg);
                                    }
                                }
                            } else {
                                Either::Left(DestructData::Implicit)
                            }
                        }

                        ty::Placeholder(..) | ty::Infer(..) | ty::Error(..) => {
                            let msg = format!(
                                "Cannot resolve clause `{tref:?}` \
                                because of a type error"
                            );
                            return error(msg);
                        }
                    };
                    destruct_data.map_left(BuiltinTraitData::Destruct)
                } else {
                    Either::Left(BuiltinTraitData::Other)
                };
                match trait_data {
                    Either::Left(trait_data) => ImplExprAtom::Builtin {
                        trait_data,
                        impl_exprs,
                        types,
                    },
                    Either::Right(atom) => atom,
                }
            }
        };

        ImplExpr {
            r#impl: atom,
            r#trait: *tref,
        }
    }

    /// Resolve the predicates required by the given item.
    pub fn resolve_item_required_predicates(
        &mut self,
        def_id: DefId,
        generics: GenericArgsRef<'tcx>,
    ) -> Vec<ImplExpr<'tcx>> {
        let tcx = self.tcx;
        self.resolve_predicates(
            ItemPredicates::required_recursively(tcx, def_id, &self.options),
            generics,
        )
    }

    /// Resolve the predicates implied by the given item.
    pub fn resolve_item_implied_predicates(
        &mut self,
        def_id: DefId,
        generics: GenericArgsRef<'tcx>,
    ) -> Vec<ImplExpr<'tcx>> {
        let tcx = self.tcx;
        self.resolve_predicates(
            ItemPredicates::implied(tcx, def_id, &self.options),
            generics,
        )
    }

    /// Apply the given generics to the provided clauses and resolve the trait references in the
    /// current context.
    pub fn resolve_predicates(
        &mut self,
        predicates: ItemPredicates<'tcx>,
        generics: GenericArgsRef<'tcx>,
    ) -> Vec<ImplExpr<'tcx>> {
        let tcx = self.tcx;
        predicates
            .iter_trait_clauses()
            // Substitute the item generics
            .map(|(_, trait_ref)| EarlyBinder::bind(trait_ref).instantiate(tcx, generics))
            // Resolve
            .map(|trait_ref| self.resolve(&trait_ref))
            .collect()
    }
}

/// Attempts to resolve an obligation to an `ImplSource`. The result is a shallow `ImplSource`
/// resolution, meaning that we do not resolve all nested obligations on the impl. Note that type
/// check should guarantee to us that all nested obligations *could be* resolved if we wanted to.
///
/// This expects that `trait_ref` is fully normalized.
///
/// This is based on `rustc_traits::codegen::codegen_select_candidate` in rustc.
fn shallow_resolve_trait_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    trait_ref: PolyTraitRef<'tcx>,
) -> Result<ImplSource<'tcx, ()>, CodegenObligationError> {
    use rustc_infer::infer::TyCtxtInferExt;
    use rustc_middle::traits::CodegenObligationError;
    use rustc_middle::ty::TypeVisitableExt;
    use rustc_trait_selection::traits::{
        Obligation, ObligationCause, ObligationCtxt, SelectionContext, SelectionError,
    };
    // Do the initial selection for the obligation. This yields the
    // shallow result we are looking for -- that is, what specific impl.
    let infcx = tcx
        .infer_ctxt()
        .ignoring_regions()
        .build(TypingMode::PostAnalysis);
    let mut selcx = SelectionContext::new(&infcx);

    let obligation_cause = ObligationCause::dummy();
    let obligation = Obligation::new(tcx, obligation_cause, param_env, trait_ref);

    let selection = match selcx.poly_select(&obligation) {
        Ok(Some(selection)) => selection,
        Ok(None) => return Err(CodegenObligationError::Ambiguity),
        Err(SelectionError::Unimplemented) => return Err(CodegenObligationError::Unimplemented),
        Err(_) => return Err(CodegenObligationError::Ambiguity),
    };

    // Currently, we use a fulfillment context to completely resolve
    // all nested obligations. This is because they can inform the
    // inference of the impl's type parameters.
    // FIXME(-Znext-solver): Doesn't need diagnostics if new solver.
    let ocx = ObligationCtxt::new(&infcx);
    let impl_source = selection.map(|obligation| {
        ocx.register_obligation(obligation.clone());
    });

    let errors = ocx.evaluate_obligations_error_on_ambiguity();
    if !errors.is_empty() {
        return Err(CodegenObligationError::Ambiguity);
    }

    let impl_source = infcx.resolve_vars_if_possible(impl_source);
    let impl_source = tcx.erase_and_anonymize_regions(impl_source);

    if impl_source.has_infer() {
        // Unused lifetimes on an impl get replaced with inference vars, but never resolved.
        return Err(CodegenObligationError::Ambiguity);
    }

    Ok(impl_source)
}
