use rustc_middle::ty;
use rustc_span::def_id::DefId as RDefId;

pub use rustc_trait_elaboration as elaboration;
pub use rustc_trait_elaboration::{
    ElaborationCtx, ItemPredicate, ItemPredicateId, ItemPredicates, PredicateSearcher,
    ToPolyTraitRef, erase_and_norm, erase_free_regions, normalize, self_predicate,
};

use crate::hax::prelude::*;
use charon_lib::ast::HashConsed;

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: elaboration::ImpliedPredicate<'tcx>, state: S as s)]
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum TraitProofImpliedPredicate {
    AssocItem {
        /// Reference to the item, with generics (for GATs), e.g. the `T` and proof for `T: Clone`
        /// in the following example:
        /// ```ignore
        /// trait Foo {
        ///     type Type<T: Clone>: Debug;
        /// }
        /// ```
        item: ItemRef,
        /// The index of this predicate among the trait predicates returned by `ItemPredicates::Implied`.
        index: usize,
    },
    Parent {
        /// The index of this predicate among the trait predicates returned by `ItemPredicates::Implied`.
        index: usize,
    },
}

/// The source of a particular trait implementation. Most often this is either `Concrete` for a
/// concrete `impl Trait for Type {}` item, or `LocalBound` for a context-bound `where T: Trait`.
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: elaboration::TraitProofKind<'tcx>, state: S as s)]
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum TraitProofKind {
    /// A concrete `impl Trait for Type {}` item.
    Concrete(ItemRef),
    /// A context-bound clause like `where T: Trait`.
    LocalBound(GenericPredicateId),
    /// The implicit `Self: Trait` clause present inside a `trait Trait {}` item.
    // TODO: should we also get that clause for trait impls?
    SelfProof,
    /// `dyn Trait` is a wrapped value with a virtual table for trait
    /// `Trait`.  In other words, a value `dyn Trait` is a dependent
    /// triple that gathers a type τ, a value of type τ and an
    /// instance of type `Trait`.
    /// `dyn Trait` implements `Trait` using a built-in implementation; this refers to that
    /// built-in implementation.
    Dyn,
    /// A built-in trait whose implementation is computed by the compiler, such as `FnMut`. This
    /// morally points to an invisible `impl` block; as such it contains the information we may
    /// need from one.
    Builtin {
        /// Extra data for the given trait.
        trait_data: BuiltinTraitData,
        /// The trait proofs required to satisfy the implied predicates on the trait declaration.
        /// E.g. since `FnMut: FnOnce`, a built-in `T: FnMut` impl would have a proof for
        /// `T: FnOnce`.
        proofs: Vec<TraitProof>,
        /// The values of the associated types for this trait.
        types: Vec<(DefId, Ty, Vec<TraitProof>)>,
    },
    /// A predicate implied by `base` by following `path`.
    Derived {
        base: TraitProof,
        path: TraitProofImpliedPredicate,
    },
    /// An error happened while resolving traits.
    Error(String),
}

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: elaboration::BuiltinTraitData<'tcx>, state: S as s)]
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum BuiltinTraitData {
    /// A virtual `Destruct` implementation.
    /// `Destruct` is implemented automatically for all types. For our purposes, we chose to attach
    /// the information about `drop_in_place` to that trait. This data tells us what kind of
    /// `drop_in_place` the target type has.
    Destruct(DestructData),
    /// An auto-trait.
    Auto,
    /// Some other builtin trait.
    Other,
}

#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: elaboration::DestructData<'tcx>, state: S as s)]
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum DestructData {
    /// A drop that does nothing, e.g. for scalars and pointers.
    Noop,
    /// An implicit `Destruct` local clause, if the `resolve_destruct_bounds` option is `false`. If
    /// that option is `true`, we'll add `Destruct` bounds to every type param, and use that to
    /// resolve `Destruct` impls of generics. If it's `false`, we use this variant to indicate that
    /// the clause comes from a generic or associated type.
    Implicit,
    /// The `drop_in_place` is known and non-trivial.
    Glue {
        /// The type we're generating glue for.
        ty: Ty,
    },
}

/// A `TraitProof` describes the full data of a trait implementation. Because of generics, this may
/// need to combine several concrete trait implementation items. For example, `((1u8, 2u8),
/// "hello").clone()` combines the generic implementation of `Clone` for `(A, B)` with the
/// concrete implementations for `u8` and `&str`, represented as a tree.
pub type TraitProof = HashConsed<TraitProofContents>;

#[derive(Clone, Debug, Hash, PartialEq, Eq, AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx> >, from: elaboration::TraitProofContents<'tcx>, state: S as s)]
pub struct TraitProofContents {
    /// The trait predicate this is an impl for.
    pub pred: Binder<TraitRef>,
    /// The kind of implemention of the root of the tree.
    pub kind: TraitProofKind,
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, TraitProof> for elaboration::TraitProof<'tcx> {
    fn sinto(&self, s: &S) -> TraitProof {
        HashConsed::new(self.contents().sinto(s))
    }
}

/// Given a clause `clause` in the context of some impl block `impl_did`, susbts correctly `Self`
/// from `clause` and (1) derive a `Clause` and (2) resolve a `TraitProof`.
pub fn super_clause_to_clause_and_trait_proof<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    impl_did: rustc_span::def_id::DefId,
    clause: rustc_middle::ty::Clause<'tcx>,
    span: rustc_span::Span,
) -> Option<(Clause, TraitProof, Span)> {
    let tcx = s.base().tcx;
    if !matches!(
        tcx.def_kind(impl_did),
        rustc_hir::def::DefKind::Impl { of_trait: true }
    ) {
        return None;
    }
    let impl_trait_ref =
        rustc_middle::ty::Binder::dummy(tcx.impl_trait_ref(impl_did).instantiate_identity());
    let new_clause = clause.instantiate_supertrait(tcx, impl_trait_ref);
    let trait_proof = solve_trait(
        s,
        new_clause
            .as_predicate()
            .as_trait_clause()?
            .to_poly_trait_ref(),
    );
    let new_clause = new_clause.sinto(s);
    Some((new_clause, trait_proof, span.sinto(s)))
}

/// This is the entrypoint of the solving.
#[tracing::instrument(level = "trace", skip(s))]
pub fn solve_trait<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    trait_ref: rustc_middle::ty::PolyTraitRef<'tcx>,
) -> TraitProof {
    if let Some(trait_proof) = s.with_cache(|cache| cache.trait_proofs.get(&trait_ref).cloned()) {
        return trait_proof;
    }
    let trait_proof = s.with_predicate_searcher(|pred_searcher| pred_searcher.resolve(&trait_ref));
    let trait_proof: TraitProof = trait_proof.sinto(s);
    s.with_cache(|cache| cache.trait_proofs.insert(trait_ref, trait_proof.clone()));
    trait_proof
}

/// Translate a reference to an item, resolving the appropriate trait clauses as needed.
#[tracing::instrument(level = "trace", skip(s), ret)]
pub fn translate_item_ref<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
    generics: ty::GenericArgsRef<'tcx>,
) -> ItemRef {
    ItemRef::translate(s, def_id, generics)
}

/// Solve the trait obligations for a specific item use (for example, a method call, an ADT, etc.)
/// in the current context. Just like generic args include generics of parent items, this includes
/// trait proofs for parent items.
#[tracing::instrument(level = "trace", skip(s), ret)]
pub fn solve_item_required_traits<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
    generics: ty::GenericArgsRef<'tcx>,
) -> Vec<TraitProof> {
    let predicates = ItemPredicates::required_recursively(s.base().elab_ctx, def_id);
    solve_item_traits_inner(s, generics, predicates)
}

/// Solve the trait obligations for implementing a trait (or for trait associated type bounds) in
/// the current context.
#[tracing::instrument(level = "trace", skip(s), ret)]
pub fn solve_item_implied_traits<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
    generics: ty::GenericArgsRef<'tcx>,
) -> Vec<TraitProof> {
    let predicates = ItemPredicates::implied(s.base().elab_ctx, def_id);
    solve_item_traits_inner(s, generics, predicates)
}

/// Apply the given generics to the provided clauses and resolve the trait references in the
/// current context.
fn solve_item_traits_inner<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    generics: ty::GenericArgsRef<'tcx>,
    predicates: ItemPredicates<'tcx>,
) -> Vec<TraitProof> {
    let tcx = s.base().tcx;
    let typing_env = s.typing_env();
    predicates
        .iter_trait_clauses()
        // Substitute the item generics
        .map(|(_, trait_ref)| ty::EarlyBinder::bind(trait_ref).instantiate(tcx, generics))
        .map(|trait_ref| normalize(tcx, typing_env, trait_ref))
        // Resolve
        .map(|trait_ref| solve_trait(s, trait_ref))
        .collect()
}

/// Retrieve the `Self: Trait` clause for a trait associated item.
pub fn self_clause_for_item<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
    generics: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Option<TraitProof> {
    let tcx = s.base().tcx;

    let tr_def_id = tcx.trait_of_assoc(def_id)?;
    // The "self" predicate in the context of the trait.
    let self_pred = self_predicate(tcx, tr_def_id);
    // Substitute to be in the context of the current item.
    let generics = generics.truncate_to(tcx, tcx.generics_of(tr_def_id));
    let self_pred = ty::EarlyBinder::bind(self_pred).instantiate(tcx, generics);

    // Resolve
    Some(solve_trait(s, self_pred))
}

/// Solve the `T: Sized` predicate.
pub fn solve_sized<'tcx, S: UnderOwnerState<'tcx>>(s: &S, ty: ty::Ty<'tcx>) -> TraitProof {
    let tcx = s.base().tcx;
    let sized_trait = tcx.lang_items().sized_trait().unwrap();
    let ty = erase_free_regions(tcx, ty);
    let tref = ty::Binder::dummy(ty::TraitRef::new(tcx, sized_trait, [ty]));
    solve_trait(s, tref)
}

/// Solve the `T: Destruct` predicate.
pub fn solve_destruct<'tcx, S: UnderOwnerState<'tcx>>(s: &S, ty: ty::Ty<'tcx>) -> TraitProof {
    let tcx = s.base().tcx;
    let destruct_trait = tcx.lang_items().destruct_trait().unwrap();
    let tref = ty::Binder::dummy(ty::TraitRef::new(tcx, destruct_trait, [ty]));
    solve_trait(s, tref)
}
