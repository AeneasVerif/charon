use rustc_arena::TypedArena;
use rustc_data_structures::sharded::ShardedHashMap;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;
use std::cell::{RefCell, RefMut};

use crate::{BoundsOptions, ItemPredicates, PredicateSearcher, TraitProof, TraitProofContents};

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

#[derive(Clone, Copy)]
pub struct ElaborationCtx<'tcx> {
    pub tcx: ty::TyCtxt<'tcx>,
    data: &'tcx ElaborationData<'tcx>,
}

#[derive(Default)]
struct ElaborationData<'tcx> {
    bounds_options: BoundsOptions,
    trait_proofs: intern::TraitProofInterner<'tcx>,
    trait_proofs_arena: TypedArena<TraitProofContents<'tcx>>,
    predicate_searchers: RefCell<FxHashMap<DefId, PredicateSearcher<'tcx>>>,
    required_predicates: PredicateCache<'tcx>,
    required_recursively_predicates: PredicateCache<'tcx>,
    implied_predicates: PredicateCache<'tcx>,
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

impl<'tcx> ElaborationData<'tcx> {
    fn intern_trait_proof(&'tcx self, contents: TraitProofContents<'tcx>) -> TraitProof<'tcx> {
        let interned = self
            .trait_proofs
            .intern(contents, |contents| self.trait_proofs_arena.alloc(contents));
        TraitProof { contents: interned }
    }
}

impl<'tcx> ElaborationCtx<'tcx> {
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

    pub fn predicate_searcher_for(&self, def_id: DefId) -> RefMut<'_, PredicateSearcher<'tcx>> {
        let mut predicate_searchers = self.data.predicate_searchers.borrow_mut();
        predicate_searchers
            .entry(def_id)
            .or_insert_with(|| PredicateSearcher::new_for_owner(*self, def_id));
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
