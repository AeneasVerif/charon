use rustc_data_structures::sharded::ShardedHashMap;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;
use std::cell::{RefCell, RefMut};

use crate::{
    AssocItemResolution, BoundsOptions, ItemId, ItemPredicates, ItemRef, PredicateSearcher,
    TraitProof, TraitProofContents,
};

pub mod intern {
    use rustc_arena::TypedArena;
    use rustc_data_structures::intern::Interned;
    use rustc_data_structures::sharded::{IntoPointer, ShardedHashMap};
    use std::borrow::Borrow;
    use std::hash::{Hash, Hasher};

    /// Storage for deduplicated values. The values handed out are compared by address.
    pub struct Interner<'tcx, T: Eq + Hash> {
        values: ShardedHashMap<InternedValue<'tcx, T>, ()>,
        arena: TypedArena<T>,
    }

    impl<'tcx, T: Eq + Hash> Default for Interner<'tcx, T> {
        fn default() -> Self {
            Self {
                values: Default::default(),
                arena: Default::default(),
            }
        }
    }

    impl<'tcx, T: Eq + Hash> Interner<'tcx, T> {
        pub fn intern(&'tcx self, value: T) -> Interned<'tcx, T> {
            let interned = self
                .values
                .intern(value, |value| InternedValue(self.arena.alloc(value)));
            Interned::new_unchecked(interned.0)
        }
    }

    // This mirrors rustc's `InternedInSet`: the value lives in the arena and the set stores this
    // copyable pointer wrapper. Equality and hashing still use the pointed-to contents, so
    // `ShardedHashMap::intern` can find an existing arena value if any.
    struct InternedValue<'tcx, T>(&'tcx T);

    impl<T> Clone for InternedValue<'_, T> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<T> Copy for InternedValue<'_, T> {}

    impl<T> IntoPointer for InternedValue<'_, T> {
        fn into_pointer(&self) -> *const () {
            self.0 as *const T as *const ()
        }
    }

    impl<T> Borrow<T> for InternedValue<'_, T> {
        fn borrow(&self) -> &T {
            self.0
        }
    }

    impl<T: Eq> PartialEq for InternedValue<'_, T> {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    impl<T: Eq> Eq for InternedValue<'_, T> {}

    impl<T: Hash> Hash for InternedValue<'_, T> {
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

pub type ItemRefKey<'tcx, Id> = (Id, ty::GenericArgsRef<'tcx>, AssocItemResolution);

struct ElaborationData<'tcx, Id: ItemId = DefId> {
    bounds_options: BoundsOptions,
    trait_proofs: intern::Interner<'tcx, TraitProofContents<'tcx, Id>>,
    predicate_searchers: RefCell<FxHashMap<Id, PredicateSearcher<'tcx, Id>>>,
    concrete_item_refs: RefCell<FxHashMap<ItemRefKey<'tcx, Id>, ItemRef<'tcx, Id>>>,
    concrete_trait_proofs: RefCell<FxHashMap<ty::PolyTraitRef<'tcx>, TraitProof<'tcx, Id>>>,
    required_predicates: PredicateCache<'tcx, Id>,
    required_recursively_predicates: PredicateCache<'tcx, Id>,
    implied_predicates: PredicateCache<'tcx, Id>,
}

impl<'tcx, Id: ItemId> Default for ElaborationData<'tcx, Id> {
    fn default() -> Self {
        Self {
            bounds_options: Default::default(),
            trait_proofs: Default::default(),
            predicate_searchers: Default::default(),
            concrete_item_refs: Default::default(),
            concrete_trait_proofs: Default::default(),
            required_predicates: Default::default(),
            required_recursively_predicates: Default::default(),
            implied_predicates: Default::default(),
        }
    }
}

struct PredicateCache<'tcx, Id: ItemId> {
    values: ShardedHashMap<Id, ItemPredicates<'tcx, Id>>,
}

impl<'tcx, Id: ItemId> Default for PredicateCache<'tcx, Id> {
    fn default() -> Self {
        Self {
            values: Default::default(),
        }
    }
}

impl<'tcx, Id: ItemId> PredicateCache<'tcx, Id> {
    fn get_or_insert_with(
        &'tcx self,
        def_id: Id,
        compute: impl FnOnce() -> ItemPredicates<'tcx, Id>,
    ) -> ItemPredicates<'tcx, Id> {
        if let Some(predicates) = self.values.get(&def_id) {
            return predicates;
        }
        let predicates = compute();
        self.values.insert_unique(def_id, predicates.clone());
        predicates
    }
}

impl<'tcx, Id: ItemId> ElaborationData<'tcx, Id> {
    fn intern_trait_proof(
        &'tcx self,
        contents: TraitProofContents<'tcx, Id>,
    ) -> TraitProof<'tcx, Id> {
        let interned = self.trait_proofs.intern(contents);
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

    pub(crate) fn concrete_item_refs(
        &self,
    ) -> &'tcx RefCell<FxHashMap<ItemRefKey<'tcx, Id>, ItemRef<'tcx, Id>>> {
        &self.data.concrete_item_refs
    }

    pub(crate) fn concrete_trait_proofs(
        &self,
    ) -> &'tcx RefCell<FxHashMap<ty::PolyTraitRef<'tcx>, TraitProof<'tcx, Id>>> {
        &self.data.concrete_trait_proofs
    }

    pub fn intern_trait_proof(
        &self,
        contents: TraitProofContents<'tcx, Id>,
    ) -> TraitProof<'tcx, Id> {
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
        def_id: Id,
        compute: impl FnOnce() -> ItemPredicates<'tcx, Id>,
    ) -> ItemPredicates<'tcx, Id> {
        self.data
            .required_predicates
            .get_or_insert_with(def_id, compute)
    }

    pub(crate) fn cached_required_recursively_predicates(
        &self,
        def_id: Id,
        compute: impl FnOnce() -> ItemPredicates<'tcx, Id>,
    ) -> ItemPredicates<'tcx, Id> {
        self.data
            .required_recursively_predicates
            .get_or_insert_with(def_id, compute)
    }

    pub(crate) fn cached_implied_predicates(
        &self,
        def_id: Id,
        compute: impl FnOnce() -> ItemPredicates<'tcx, Id>,
    ) -> ItemPredicates<'tcx, Id> {
        self.data
            .implied_predicates
            .get_or_insert_with(def_id, compute)
    }
}
