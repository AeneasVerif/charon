//! Trait resolution: given a trait reference, we track which local clause caused it to be true.

use crate::*;
use itertools::{Either, Itertools};
use std::collections::{HashMap, hash_map::Entry};

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
fn initial_self_pred<'tcx, Id: ItemId>(
    state: &Id::State<'tcx>,
    def_id: &Id,
) -> Option<PolyTraitRef<'tcx>> {
    if let Some(parent) = def_id.parent_of_assoc(state) {
        if def_id.takes_explicit_self_clause(state) {
            None
        } else {
            parent.self_pred(state)
        }
    } else {
        def_id.self_pred(state)
    }
}

#[tracing::instrument(level = "trace", skip(elab_ctx))]
fn parents_trait_predicates<'tcx>(
    elab_ctx: ElaborationCtx<'tcx>,
    self_trait_ref: PolyTraitRef<'tcx>,
) -> Vec<PolyTraitRef<'tcx>> {
    let tcx = elab_ctx.tcx;
    ItemPredicates::implied(elab_ctx, self_trait_ref.def_id())
        .iter()
        // Substitute with the `self` args so that the clause makes sense in the
        // outside context.
        .map(|pred| pred.clause.instantiate_supertrait(tcx, self_trait_ref))
        .filter_map(|pred| pred.as_trait_clause())
        .map(|pred| pred.to_poly_trait_ref())
        .collect()
}

/// A trait proof we have in our context.
#[derive(Debug, Clone)]
struct Candidate<'tcx> {
    /// This is the same predicate as `origin.pred`, but normalized and erased for comparison.
    pred: PolyTraitRef<'tcx>,
    proof: TraitProof<'tcx>,
}

impl<'tcx> TraitProof<'tcx> {
    fn push(
        self,
        elab_ctx: ElaborationCtx<'tcx>,
        new_pred: PolyTraitRef<'tcx>,
        path_chunk: ImpliedPredicate<'tcx>,
    ) -> Self {
        elab_ctx.intern_trait_proof(TraitProofContents {
            pred: new_pred,
            kind: TraitProofKind::Derived {
                base: self,
                path: path_chunk,
            },
        })
    }
}

impl<'tcx> Candidate<'tcx> {
    fn from_trait_proof(origin: TraitProof<'tcx>) -> Self {
        Candidate {
            pred: origin.pred,
            proof: origin,
        }
    }

    fn push(
        &self,
        elab_ctx: ElaborationCtx<'tcx>,
        new_pred: PolyTraitRef<'tcx>,
        path_chunk: ImpliedPredicate<'tcx>,
    ) -> Self {
        Candidate {
            pred: new_pred,
            proof: self.proof.push(elab_ctx, new_pred, path_chunk),
        }
    }
}

/// Stores a set of predicates along with where they came from.
#[derive(Clone)]
pub struct PredicateSearcher<'tcx, Id: ItemId = DefId> {
    pub(crate) elab_ctx: ElaborationCtx<'tcx>,
    pub(crate) typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    /// Local clauses available in the current context.
    candidates: HashMap<PolyTraitRef<'tcx>, Candidate<'tcx>>,
    /// Whether we're in a trait declaration context where an implicit `Self: Trait` clause is
    /// accessible.
    implicit_self_clause: bool,
    /// Cache the `ItemRef` translations. This is fast because `GenericArgsRef` is interned.
    pub(crate) item_refs_cache:
        HashMap<(Id, ty::GenericArgsRef<'tcx>, AssocItemResolution), ItemRef<'tcx, Id>>,
    /// Cache of trait refs to resolved trait proofs.
    trait_proofs_cache: HashMap<ty::PolyTraitRef<'tcx>, TraitProof<'tcx>>,
}

impl<'tcx, Id: ItemId> PredicateSearcher<'tcx, Id> {
    /// Initialize the elaborator with the predicates accessible within this item.
    pub fn new_for_owner(
        elab_ctx: ElaborationCtx<'tcx>,
        state: &Id::State<'tcx>,
        owner_id: Id,
    ) -> Self {
        let initial_self_pred = initial_self_pred(state, &owner_id);
        let mut out = Self {
            elab_ctx,
            typing_env: TypingEnv::new(owner_id.param_env(state), TypingMode::PostAnalysis),
            candidates: Default::default(),
            implicit_self_clause: initial_self_pred.is_some(),
            item_refs_cache: Default::default(),
            trait_proofs_cache: Default::default(),
        };
        out.insert_predicates(initial_self_pred.map(|clause| ItemClause {
            id: ItemPredicateId::TraitSelf,
            clause,
        }));
        out.insert_bound_predicates(owner_id.required_predicates(state).predicates);
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
        let elab_ctx = self.elab_ctx;
        let implicit_self_clause = self.implicit_self_clause;
        self.insert_candidates(preds.into_iter().map(|clause| {
            let origin = elab_ctx.intern_trait_proof(TraitProofContents {
                pred: clause.clause,
                kind: match clause.id {
                    ItemPredicateId::TraitSelf if implicit_self_clause => TraitProofKind::SelfProof,
                    _ => TraitProofKind::LocalBound(clause.id),
                },
            });
            Candidate::from_trait_proof(origin)
        }))
    }

    /// Insert new candidates and all their parent predicates. This deduplicates predicates
    /// to avoid divergence.
    fn insert_candidates(&mut self, candidates: impl IntoIterator<Item = Candidate<'tcx>>) {
        let tcx = self.elab_ctx.tcx;
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
        let elab_ctx = self.elab_ctx;
        // Then recursively add their parents. This way ensures a breadth-first order,
        // which means we select the shortest path when looking up predicates.
        self.insert_candidates(new_candidates.into_iter().flat_map(|candidate| {
            parents_trait_predicates(elab_ctx, candidate.pred)
                .into_iter()
                .enumerate()
                .map(move |(index, parent_pred)| {
                    candidate.push(elab_ctx, parent_pred, ImpliedPredicate::Parent { index })
                })
        }));
    }

    /// If the type is a trait associated type, we add any relevant bounds to our context.
    fn add_associated_type_refs(&mut self, state: &Id::State<'tcx>, ty: Binder<'tcx, Ty<'tcx>>) {
        let elab_ctx = self.elab_ctx;
        let tcx = self.elab_ctx.tcx;
        // Note: We skip a binder but rebind it just after.
        let TyKind::Alias(
            alias @ ty::AliasTy {
                kind: AliasTyKind::Projection { def_id, .. },
                args,
                ..
            },
        ) = ty.skip_binder().kind()
        else {
            return;
        };
        let trait_ref = ty.rebind(alias.trait_ref(tcx)).upcast(tcx);

        // The predicate we're looking for is is `<T as Trait>::Type: OtherTrait`. We try to solve
        // `T as Trait` and add all the bounds on `Trait::Type` to our context.
        let proof = self.resolve(state, &trait_ref);
        if matches!(proof.kind, TraitProofKind::Error(_)) {
            return;
        }
        let item_ref =
            self.resolve_rust_item_reference(state, *def_id, args, AssocItemResolution::ImplItem);

        // The bounds that hold on the associated type.
        let item_bounds = ItemPredicates::implied(self.elab_ctx, *def_id);
        let item_bounds = item_bounds
            .iter_trait_clauses()
            // Substitute the item generics
            .map(|(_, tref)| {
                EarlyBinder::bind(tref)
                    .instantiate(tcx, args)
                    .skip_normalization()
            })
            .enumerate();

        // Add all the bounds on the corresponding associated item.
        self.insert_candidates(item_bounds.map(|(index, pred)| {
            Candidate::from_trait_proof(proof.push(
                elab_ctx,
                pred,
                ImpliedPredicate::AssocItem {
                    item: item_ref.clone(),
                    index,
                },
            ))
        }));
    }

    /// Resolve a local clause by looking it up in this set. If the predicate applies to an
    /// associated type, we add the relevant implied associated type bounds to the set as well.
    fn resolve_local(
        &mut self,
        state: &Id::State<'tcx>,
        target: PolyTraitRef<'tcx>,
    ) -> Option<Candidate<'tcx>> {
        tracing::trace!("Looking for {target:?}");

        // Look up the predicate
        let ret = self.candidates.get(&target).cloned();
        if ret.is_some() {
            return ret;
        }

        // Add clauses related to associated type in the `Self` type of the predicate.
        self.add_associated_type_refs(state, target.self_ty());

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
    #[tracing::instrument(level = "trace", skip(self, state))]
    pub fn resolve(
        &mut self,
        state: &Id::State<'tcx>,
        tref: &PolyTraitRef<'tcx>,
    ) -> TraitProof<'tcx> {
        if let Some(trait_proof) = self.trait_proofs_cache.get(tref).copied() {
            return trait_proof;
        }
        use rustc_trait_selection::traits::{
            BuiltinImplSource, ImplSource, ImplSourceUserDefinedData,
        };
        let tcx = self.elab_ctx.tcx;
        let destruct_trait = tcx.lang_items().destruct_trait().unwrap();

        let erased_tref = normalize_bound_val(tcx, self.typing_env, *tref);
        let trait_def_id = erased_tref.skip_binder().def_id;

        let elab_ctx = self.elab_ctx;
        let error = |msg: String| {
            elab_ctx.intern_trait_proof(TraitProofContents {
                pred: *tref,
                kind: TraitProofKind::Error(msg),
            })
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
            }) => TraitProofKind::Concrete(self.resolve_rust_item_reference(
                state,
                impl_def_id,
                generics,
                AssocItemResolution::ImplItem,
            )),
            ImplSource::Param(_) => match self.resolve_local(state, erased_tref.upcast(tcx)) {
                Some(candidate) => candidate.proof.kind.clone(),
                None => {
                    let msg =
                        format!("Could not find a clause for `{tref:?}` in the item parameters");
                    return error(msg);
                }
            },
            ImplSource::Builtin(BuiltinImplSource::Object { .. }, _) => TraitProofKind::Dyn,
            ImplSource::Builtin(_, _) => {
                // Resolve the predicates implied by the trait.
                // If we wanted to not skip this binder, we'd have to instantiate the bound
                // regions, solve, then wrap the result in a binder. And track higher-kinded
                // clauses better all over.
                let trait_proofs = self.resolve_item_implied_predicates(
                    state,
                    trait_def_id,
                    erased_tref.skip_binder().args,
                );
                let types = tcx
                    .associated_items(trait_def_id)
                    .in_definition_order()
                    .filter(|assoc| matches!(assoc.kind, AssocKind::Type { .. }))
                    .filter_map(|assoc| {
                        let ty =
                            Ty::new_projection(tcx, assoc.def_id, erased_tref.skip_binder().args);
                        let ty = crate::erase_and_norm(tcx, self.typing_env, Unnormalized::new(ty));
                        if let TyKind::Alias(alias_ty) = ty.kind()
                            && alias_ty.kind.def_id() == assoc.def_id
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
                        let trait_proofs = self.resolve_item_implied_predicates(
                            state,
                            assoc.def_id,
                            erased_tref.skip_binder().args,
                        );
                        Some((assoc.def_id, ty, trait_proofs))
                    })
                    .collect();

                let trait_data = if trait_def_id == destruct_trait {
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
                        ty::Dynamic(..) => Either::Right(TraitProofKind::Dyn),
                        ty::Param(..) | ty::Alias(..) | ty::Bound(..) => {
                            if self.elab_ctx.bounds_options().add_destruct_bounds {
                                // We've added `Destruct` impls on everything, we should be able to resolve
                                // it.
                                match self.resolve_local(state, erased_tref.upcast(tcx)) {
                                    Some(candidate) => Either::Right(candidate.proof.kind.clone()),
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
                    Either::Left(if tcx.trait_is_auto(trait_def_id) {
                        BuiltinTraitData::Auto
                    } else {
                        BuiltinTraitData::Other
                    })
                };
                match trait_data {
                    Either::Left(trait_data) => TraitProofKind::Builtin {
                        trait_data,
                        proofs: trait_proofs,
                        types,
                    },
                    Either::Right(atom) => atom,
                }
            }
        };

        let trait_proof = self.elab_ctx.intern_trait_proof(TraitProofContents {
            kind: atom,
            pred: *tref,
        });
        self.trait_proofs_cache.insert(*tref, trait_proof);
        trait_proof
    }

    /// Resolve the predicates required by the given item.
    pub fn resolve_item_required_predicates(
        &mut self,
        state: &Id::State<'tcx>,
        def_id: Id,
        generics: GenericArgsRef<'tcx>,
    ) -> Vec<TraitProof<'tcx>> {
        self.resolve_predicates(state, def_id.required_predicates(state), generics)
    }

    /// Resolve the predicates implied by the given item.
    pub fn resolve_item_implied_predicates(
        &mut self,
        state: &Id::State<'tcx>,
        def_id: DefId,
        generics: GenericArgsRef<'tcx>,
    ) -> Vec<TraitProof<'tcx>> {
        self.resolve_predicates(
            state,
            ItemPredicates::implied(self.elab_ctx, def_id),
            generics,
        )
    }

    /// Apply the given generics to the provided clauses and resolve the trait references in the
    /// current context.
    pub fn resolve_predicates(
        &mut self,
        state: &Id::State<'tcx>,
        predicates: ItemPredicates<'tcx>,
        generics: GenericArgsRef<'tcx>,
    ) -> Vec<TraitProof<'tcx>> {
        let tcx = self.elab_ctx.tcx;
        predicates
            .iter_trait_clauses()
            // Substitute the item generics
            .map(|(_, trait_ref)| {
                EarlyBinder::bind(trait_ref)
                    .instantiate(tcx, generics)
                    .skip_normalization()
            })
            // Resolve
            .map(|trait_ref| self.resolve(state, &trait_ref))
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
