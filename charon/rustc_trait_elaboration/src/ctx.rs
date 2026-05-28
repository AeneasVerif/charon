use rustc_arena::TypedArena;
use rustc_data_structures::sharded::ShardedHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;

use crate::{BoundsOptions, ImplExpr, ImplExprContents, ItemPredicates};

mod intern {
    use rustc_data_structures::intern::Interned;
    use rustc_data_structures::sharded::{IntoPointer, ShardedHashMap};
    use std::borrow::Borrow;
    use std::hash::{Hash, Hasher};

    use crate::ImplExprContents;

    #[derive(Default)]
    pub struct ImplExprInterner<'tcx>(ShardedHashMap<InternedImplExpr<'tcx>, ()>);

    impl<'tcx> ImplExprInterner<'tcx> {
        pub(crate) fn intern(
            &self,
            contents: ImplExprContents<'tcx>,
            f: impl Fn(ImplExprContents<'tcx>) -> &'tcx ImplExprContents<'tcx>,
        ) -> Interned<'tcx, ImplExprContents<'tcx>> {
            let interned = self
                .0
                .intern(contents, |contents| InternedImplExpr(f(contents)));
            Interned::new_unchecked(interned.0)
        }
    }

    // This mirrors rustc's `InternedInSet`: the value lives in the arena and the set stores this
    // copyable pointer wrapper. Equality and hashing still use the pointed-to contents, so
    // `ShardedHashMap::intern` can find an existing arena value before allocating a new one.
    struct InternedImplExpr<'tcx>(&'tcx ImplExprContents<'tcx>);

    impl<'tcx> Clone for InternedImplExpr<'tcx> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<'tcx> Copy for InternedImplExpr<'tcx> {}

    impl<'tcx> IntoPointer for InternedImplExpr<'tcx> {
        fn into_pointer(&self) -> *const () {
            self.0 as *const _ as *const ()
        }
    }

    impl<'tcx> Borrow<ImplExprContents<'tcx>> for InternedImplExpr<'tcx> {
        fn borrow(&self) -> &ImplExprContents<'tcx> {
            self.0
        }
    }

    impl<'tcx> PartialEq for InternedImplExpr<'tcx> {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    impl<'tcx> Eq for InternedImplExpr<'tcx> {}

    impl<'tcx> Hash for InternedImplExpr<'tcx> {
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
    impl_exprs: intern::ImplExprInterner<'tcx>,
    impl_exprs_arena: TypedArena<ImplExprContents<'tcx>>,
    required_predicates: PredicateCache<'tcx>,
    required_recursively_predicates: PredicateCache<'tcx>,
    implied_predicates: PredicateCache<'tcx>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct PredicateCacheKey {
    def_id: DefId,
    options: BoundsOptions,
}

#[derive(Default)]
struct PredicateCache<'tcx> {
    values: ShardedHashMap<PredicateCacheKey, ItemPredicates<'tcx>>,
}

impl<'tcx> PredicateCache<'tcx> {
    fn get_or_insert_with(
        &'tcx self,
        def_id: DefId,
        options: &BoundsOptions,
        compute: impl FnOnce() -> ItemPredicates<'tcx>,
    ) -> ItemPredicates<'tcx> {
        let key = PredicateCacheKey {
            def_id,
            options: options.clone(),
        };
        if let Some(predicates) = self.values.get(&key) {
            return predicates;
        }
        let predicates = compute();
        let _ = self.values.insert(key, predicates.clone());
        predicates
    }
}

impl<'tcx> ElaborationData<'tcx> {
    fn intern_impl_expr(&'tcx self, contents: ImplExprContents<'tcx>) -> ImplExpr<'tcx> {
        let interned = self
            .impl_exprs
            .intern(contents, |contents| self.impl_exprs_arena.alloc(contents));
        ImplExpr { contents: interned }
    }
}

impl<'tcx> ElaborationCtx<'tcx> {
    /// Warning: only create a single one.
    pub fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        // `ImplExpr` is a copyable `Interned<'tcx, _>` and may outlive the `PredicateSearcher`
        // that produced it. We therefore give each elaboration context session-long storage, like
        // rustc's own arenas. The interned values still contain rustc data bounded by `'tcx`.
        let data = Box::leak(Box::new(ElaborationData::default()));
        ElaborationCtx { tcx, data }
    }

    pub fn intern_impl_expr(&self, contents: ImplExprContents<'tcx>) -> ImplExpr<'tcx> {
        self.data.intern_impl_expr(contents)
    }

    pub(crate) fn cached_required_predicates(
        &self,
        def_id: DefId,
        options: &BoundsOptions,
        compute: impl FnOnce() -> ItemPredicates<'tcx>,
    ) -> ItemPredicates<'tcx> {
        self.data
            .required_predicates
            .get_or_insert_with(def_id, options, compute)
    }

    pub(crate) fn cached_required_recursively_predicates(
        &self,
        def_id: DefId,
        options: &BoundsOptions,
        compute: impl FnOnce() -> ItemPredicates<'tcx>,
    ) -> ItemPredicates<'tcx> {
        self.data
            .required_recursively_predicates
            .get_or_insert_with(def_id, options, compute)
    }

    pub(crate) fn cached_implied_predicates(
        &self,
        def_id: DefId,
        options: &BoundsOptions,
        compute: impl FnOnce() -> ItemPredicates<'tcx>,
    ) -> ItemPredicates<'tcx> {
        self.data
            .implied_predicates
            .get_or_insert_with(def_id, options, compute)
    }
}
