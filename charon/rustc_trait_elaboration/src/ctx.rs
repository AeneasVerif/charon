use rustc_arena::TypedArena;
use rustc_data_structures::sharded::ShardedHashMap;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;
use std::cell::{RefCell, RefMut};

use crate::{
    BoundsOptions, ItemId, ItemPredicates, PredicateSearcher, TraitProof, TraitProofContents,
};

mod intern {
    use rustc_data_structures::intern::Interned;
    use rustc_data_structures::sharded::{IntoPointer, ShardedHashMap};
    use std::borrow::Borrow;
    use std::hash::{Hash, Hasher};

    use crate::TraitProofContents;

    #[derive(Default)]
    pub struct TraitProofInterner<'tcx>(ShardedHashMap<InternedTraitProof<'tcx>, ()>);

    impl<'tcx> TraitProofInterner<'tcx> {
        pub(crate) fn intern(
            &self,
            contents: TraitProofContents<'tcx>,
            f: impl Fn(TraitProofContents<'tcx>) -> &'tcx TraitProofContents<'tcx>,
        ) -> Interned<'tcx, TraitProofContents<'tcx>> {
            let interned = self
                .0
                .intern(contents, |contents| InternedTraitProof(f(contents)));
            Interned::new_unchecked(interned.0)
        }
    }

    // This mirrors rustc's `InternedInSet`: the value lives in the arena and the set stores this
    // copyable pointer wrapper. Equality and hashing still use the pointed-to contents, so
    // `ShardedHashMap::intern` can find an existing arena value before allocating a new one.
    struct InternedTraitProof<'tcx>(&'tcx TraitProofContents<'tcx>);

    impl<'tcx> Clone for InternedTraitProof<'tcx> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<'tcx> Copy for InternedTraitProof<'tcx> {}

    impl<'tcx> IntoPointer for InternedTraitProof<'tcx> {
        fn into_pointer(&self) -> *const () {
            self.0 as *const _ as *const ()
        }
    }

    impl<'tcx> Borrow<TraitProofContents<'tcx>> for InternedTraitProof<'tcx> {
        fn borrow(&self) -> &TraitProofContents<'tcx> {
            self.0
        }
    }

    impl<'tcx> PartialEq for InternedTraitProof<'tcx> {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    impl<'tcx> Eq for InternedTraitProof<'tcx> {}

    impl<'tcx> Hash for InternedTraitProof<'tcx> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.0.hash(state);
        }
    }
}

pub struct ElaborationCtx<'tcx, Id: ItemId = DefId> {
    pub tcx: ty::TyCtxt<'tcx>,
    data: &'tcx ElaborationData<'tcx, Id>,
}

impl<'tcx, Id: ItemId> Clone for ElaborationCtx<'tcx, Id> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'tcx, Id: ItemId> Copy for ElaborationCtx<'tcx, Id> {}

struct ElaborationData<'tcx, Id: ItemId = DefId> {
    bounds_options: BoundsOptions,
    trait_proofs: intern::TraitProofInterner<'tcx>,
    trait_proofs_arena: TypedArena<TraitProofContents<'tcx>>,
    predicate_searchers: RefCell<FxHashMap<Id, PredicateSearcher<'tcx, Id>>>,
    required_predicates: PredicateCache<'tcx>,
    required_recursively_predicates: PredicateCache<'tcx>,
    implied_predicates: PredicateCache<'tcx>,
}

impl<'tcx, Id: ItemId> Default for ElaborationData<'tcx, Id> {
    fn default() -> Self {
        Self {
            bounds_options: Default::default(),
            trait_proofs: Default::default(),
            trait_proofs_arena: Default::default(),
            predicate_searchers: Default::default(),
            required_predicates: Default::default(),
            required_recursively_predicates: Default::default(),
            implied_predicates: Default::default(),
        }
    }
}

#[derive(Default)]
struct PredicateCache<'tcx> {
    values: ShardedHashMap<DefId, ItemPredicates<'tcx>>,
}

impl<'tcx> PredicateCache<'tcx> {
    fn get_or_insert_with(
        &'tcx self,
        def_id: DefId,
        compute: impl FnOnce() -> ItemPredicates<'tcx>,
    ) -> ItemPredicates<'tcx> {
        if let Some(predicates) = self.values.get(&def_id) {
            return predicates;
        }
        let predicates = compute();
        self.values.insert_unique(def_id, predicates.clone());
        predicates
    }
}

impl<'tcx, Id: ItemId> ElaborationData<'tcx, Id> {
    fn intern_trait_proof(&'tcx self, contents: TraitProofContents<'tcx>) -> TraitProof<'tcx> {
        let interned = self
            .trait_proofs
            .intern(contents, |contents| self.trait_proofs_arena.alloc(contents));
        TraitProof { contents: interned }
    }
}

impl<'tcx, Id: ItemId> ElaborationCtx<'tcx, Id> {
    /// Warning: only create a single one.
    pub fn new(tcx: ty::TyCtxt<'tcx>, bounds_options: BoundsOptions) -> Self {
        // `TraitProof` is a copyable `Interned<'tcx, _>` and may outlive the `PredicateSearcher`
        // that produced it. We therefore give each elaboration context session-long storage, like
        // rustc's own arenas. The interned values still contain rustc data bounded by `'tcx`.
        let data = Box::leak(Box::new(ElaborationData {
            bounds_options,
            ..ElaborationData::default()
        }));
        ElaborationCtx { tcx, data }
    }

    pub fn bounds_options(&self) -> &BoundsOptions {
        &self.data.bounds_options
    }

    pub fn intern_trait_proof(&self, contents: TraitProofContents<'tcx>) -> TraitProof<'tcx> {
        self.data.intern_trait_proof(contents)
    }

    pub fn predicate_searcher_for(
        &self,
        state: &Id::State<'tcx>,
        def_id: Id,
    ) -> RefMut<'_, PredicateSearcher<'tcx, Id>> {
        self.predicate_searcher_for_with(def_id.clone(), || {
            PredicateSearcher::new_for_owner(*self, state, def_id)
        })
    }

    pub fn predicate_searcher_for_with(
        &self,
        def_id: Id,
        make: impl FnOnce() -> PredicateSearcher<'tcx, Id>,
    ) -> RefMut<'_, PredicateSearcher<'tcx, Id>> {
        let mut predicate_searchers = self.data.predicate_searchers.borrow_mut();
        predicate_searchers
            .entry(def_id.clone())
            .or_insert_with(make);
        RefMut::map(predicate_searchers, |predicate_searchers| {
            predicate_searchers.get_mut(&def_id).unwrap()
        })
    }

    pub(crate) fn cached_required_predicates(
        &self,
        def_id: DefId,
        compute: impl FnOnce() -> ItemPredicates<'tcx>,
    ) -> ItemPredicates<'tcx> {
        self.data
            .required_predicates
            .get_or_insert_with(def_id, compute)
    }

    pub(crate) fn cached_required_recursively_predicates(
        &self,
        def_id: DefId,
        compute: impl FnOnce() -> ItemPredicates<'tcx>,
    ) -> ItemPredicates<'tcx> {
        self.data
            .required_recursively_predicates
            .get_or_insert_with(def_id, compute)
    }

    pub(crate) fn cached_implied_predicates(
        &self,
        def_id: DefId,
        compute: impl FnOnce() -> ItemPredicates<'tcx>,
    ) -> ItemPredicates<'tcx> {
        self.data
            .implied_predicates
            .get_or_insert_with(def_id, compute)
    }
}
