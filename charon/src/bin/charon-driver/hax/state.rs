use crate::hax::prelude::*;
use paste::paste;
use rustc_middle::ty::{self, TyCtxt};

macro_rules! mk_aux {
    ($state:ident {$($lts:lifetime)*} $field:ident {$($field_type:tt)+} {$($gen:tt)*} {$($gen_full:tt)*} {$($params:tt)*} {$($fields:tt)*}) => {
        paste ! {
            pub trait [<Has $field:camel>]<$($lts,)*> {
                fn $field(self: &Self) -> $($field_type)+<$($lts)*>;
            }
            impl<$($lts,)*$($gen)*> [<Has $field:camel>]<$($lts,)*> for $state<$($params)*> {
                fn $field(self: &Self) -> $($field_type)+<$($lts)*> {
                    self.$field.clone()
                }
            }
        }
    };
}
macro_rules! mk {
    (struct $state:ident<$($glts:lifetime),*> {$($field:ident : {$($lts:lifetime),*} $field_type:ty),*$(,)?}) => {
        mk!(@$state {} {$($field)*} {$($field: {$($lts),*} {$field_type},)*});
    };
    (@$state:ident {$($acc:tt)*} $fields:tt {
        $field:ident : $lts:tt $field_type:tt
        $(,$($rest:tt)*)?
    }) => {mk!(@$state {
        $($acc)* $fields $field: $lts $field_type,
    } $fields {$($($rest)*)?} );};
    (@$state:ident $body:tt $fields:tt {$(,)?}) => { mk! (@@ $state $body ); };
    (@@$state:ident {$({$($fields:tt)*} $field:ident : {$($lts:lifetime)*} {$($field_type:tt)+},)*}) => {
        paste! {
            #[derive(Clone)]
            pub struct $state<$([<$field:camel>],)*>{
                $(pub $field: [<$field:camel>],)*
            }
        }
        $(
            macro_rules! __inner_helper {
                ($gen:tt {$$($full_gen:tt)*} {$$($params:tt)*} $field $$($rest:tt)*) => {
                    paste! {__inner_helper!(
                        $gen {$$($full_gen)*[<$field:camel>],}
                        {$$($params)*$($field_type)+<$($lts,)*>,} $$($rest)*
                    );}
                };
                ({$$($gen:tt)*} {$$($full_gen:tt)*} {$$($params:tt)*} $i:ident $$($rest:tt)*) => {
                    paste! {__inner_helper!(
                        {$$($gen)*[<$i:camel>],} {$$($full_gen)*[<$i:camel>],}
                        {$$($params)*[<$i:camel>],} $$($rest)*
                    );}
                };
                ($gen:tt $full_gen:tt $params:tt $$(,)?) => {
                    mk_aux!($state {$($lts)*} $field {$($field_type)+} $gen $full_gen $params {$($fields)*});
                };
            }
            __inner_helper!({} {} {} $($fields)*);
        )*
    };
}

mod types {
    use crate::hax::prelude::*;
    use itertools::Itertools;
    use rustc_hash::FxHashMap;
    use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
    use rustc_middle::ty;
    use rustc_span::symbol::Symbol;
    use rustc_trait_elaboration::ElaborationCtx;
    use std::{cell::RefCell, sync::Arc};

    pub struct LocalContextS {
        pub vars: HashMap<rustc_middle::thir::LocalVarId, String>,
    }

    impl Default for LocalContextS {
        fn default() -> Self {
            Self::new()
        }
    }

    impl LocalContextS {
        pub fn new() -> LocalContextS {
            LocalContextS {
                vars: HashMap::new(),
            }
        }
    }

    /// Global caches
    #[derive(Default)]
    pub struct GlobalCache<'tcx> {
        /// Per-item cache.
        pub per_item: HashMap<DefId, ItemCache<'tcx>>,
        /// Map rustc def ids to their hax counterpart.
        pub def_ids: HashMap<RDefId, DefId>,
        /// Map that recovers rustc args for a given `ItemRef`.
        pub reverse_item_refs_map: HashMap<ItemRef, ty::GenericArgsRef<'tcx>>,
        /// We create some artificial items; their def_ids are stored here. See the
        /// `synthetic_items` module.
        pub synthetic_def_ids: HashMap<SyntheticItem, RDefId>,
        pub reverse_synthetic_map: HashMap<RDefId, SyntheticItem>,
        /// Cached names and disambiguators for crate names.
        pub disambiguated_crate_names: Option<FxHashMap<CrateNum, (Symbol, u32)>>,
    }

    impl<'tcx> GlobalCache<'tcx> {
        pub fn crate_name(&mut self, tcx: ty::TyCtxt<'tcx>, krate: CrateNum) -> (Symbol, u32) {
            self.disambiguated_crate_names
                .get_or_insert_with(|| {
                    std::iter::once(LOCAL_CRATE)
                        .chain(tcx.crates(()).iter().copied())
                        .into_group_map_by(|&cnum| tcx.crate_name(cnum))
                        .into_iter()
                        .filter(|(_, crates_by_this_name)| crates_by_this_name.len() > 1)
                        .flat_map(|(name, mut crates_by_this_name)| {
                            crates_by_this_name.sort_by_key(|&cnum| {
                                // `tcx.stable_crate_id` isn't actually so stable across machines.
                                // We try our own stability here based on paths.
                                let source_file = tcx
                                    .sess
                                    .source_map()
                                    .span_to_filename(tcx.def_span(cnum.as_def_id()))
                                    .prefer_remapped_unconditionally()
                                    .to_string_lossy()
                                    .into_owned();
                                let extern_paths = if cnum == LOCAL_CRATE {
                                    Vec::new()
                                } else {
                                    tcx.crate_extern_paths(cnum)
                                        .iter()
                                        .map(|path| path.display().to_string())
                                        .collect_vec()
                                };
                                (
                                    cnum != LOCAL_CRATE,
                                    source_file,
                                    extern_paths,
                                    cnum.as_u32(),
                                )
                            });
                            crates_by_this_name.into_iter().enumerate().map(
                                move |(disambiguator, cnum)| (cnum, (name, disambiguator as u32)),
                            )
                        })
                        .collect()
                })
                .get(&krate)
                .copied()
                .unwrap_or_else(|| (tcx.crate_name(krate), 0))
        }
    }

    /// Per-item cache
    #[derive(Default)]
    pub struct ItemCache<'tcx> {
        /// The translated definitions, generic in the Body kind.
        /// Each rustc `DefId` gives several hax `DefId`s: one for each promoted constant (if any),
        /// and the base one represented by `None`. Moreover we can instantiate definitions with
        /// generic arguments.
        pub full_defs:
            HashMap<(Option<PromotedId>, Option<ty::GenericArgsRef<'tcx>>), Arc<FullDef<'tcx>>>,
        /// Cache the `Ty` translations.
        pub tys: HashMap<ty::Ty<'tcx>, Ty>,
        /// Cache the `ItemRef` translations. This is fast because `GenericArgsRef` is interned.
        pub item_refs: HashMap<(DefId, ty::GenericArgsRef<'tcx>, AssocItemResolution), ItemRef>,
        /// Cache of trait refs to resolved trait proofs.
        pub trait_proofs: HashMap<ty::PolyTraitRef<'tcx>, crate::hax::traits::TraitProof>,
        /// Generics for this item, if it is virtual.
        pub virtual_generics: Option<&'tcx ty::Generics>,
    }

    #[derive(Clone)]
    pub struct Base<'tcx> {
        pub options: Rc<crate::hax::options::Options>,
        pub local_ctx: Rc<RefCell<LocalContextS>>,
        pub opt_def_id: Option<rustc_hir::def_id::DefId>,
        pub cache: Rc<RefCell<GlobalCache<'tcx>>>,
        pub elab_ctx: crate::hax::traits::ElaborationCtx<'tcx, DefId>,
        pub tcx: ty::TyCtxt<'tcx>,
    }

    impl<'tcx> Base<'tcx> {
        pub fn new(
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
            options: crate::hax::options::Options,
            bounds_options: crate::hax::options::BoundsOptions,
        ) -> Self {
            Self {
                tcx,
                cache: Default::default(),
                options: Rc::new(options),
                // Always prefer `s.owner_id()` to `s.base().opt_def_id`.
                // `opt_def_id` is used in `utils` for error reporting
                opt_def_id: None,
                local_ctx: Rc::new(RefCell::new(LocalContextS::new())),
                elab_ctx: ElaborationCtx::new(tcx, bounds_options),
            }
        }
    }

    pub type UnitBinder<'tcx> = rustc_middle::ty::Binder<'tcx, ()>;
}

mk!(
    struct State<'tcx> {
        base: {'tcx} types::Base,
        owner: {} DefId,
        binder: {'tcx} types::UnitBinder,
    }
);

pub use self::types::*;

pub type StateWithBase<'tcx> = State<Base<'tcx>, (), ()>;
pub type StateWithOwner<'tcx> = State<Base<'tcx>, DefId, ()>;
pub type StateWithBinder<'tcx> = State<Base<'tcx>, DefId, types::UnitBinder<'tcx>>;

impl<'tcx> StateWithBase<'tcx> {
    pub fn new(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        options: crate::hax::options::Options,
        bounds_options: crate::hax::options::BoundsOptions,
    ) -> Self {
        Self {
            base: Base::new(tcx, options, bounds_options),
            owner: (),
            binder: (),
        }
    }
}

pub trait BaseState<'tcx>: HasBase<'tcx> + Clone {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.base().tcx
    }

    /// Create a state with the given owner.
    fn with_hax_owner(&self, owner: &DefId) -> StateWithOwner<'tcx> {
        let mut base = self.base();
        base.opt_def_id = owner.as_real_or_promoted();
        State {
            owner: owner.clone(),
            base,
            binder: (),
        }
    }
    /// Create a state with the given owner.
    fn with_rustc_owner(&self, owner_id: RDefId) -> StateWithOwner<'tcx> {
        let owner = &owner_id.sinto(self);
        Self::with_hax_owner(self, owner)
    }

    /// State with only access to the global state.
    fn base_state(&self) -> StateWithBase<'tcx> {
        State {
            base: self.base(),
            owner: (),
            binder: (),
        }
    }
}
impl<'tcx, T: HasBase<'tcx> + Clone> BaseState<'tcx> for T {}

/// State of anything below an `owner`.
pub trait UnderOwnerState<'tcx>: BaseState<'tcx> + HasOwner {
    fn param_env(&self) -> ty::ParamEnv<'tcx> {
        self.owner().param_env(self)
    }
    fn typing_env(&self) -> ty::TypingEnv<'tcx> {
        self.owner().typing_env(self)
    }
    fn with_base(&self, base: types::Base<'tcx>) -> StateWithOwner<'tcx> {
        State {
            owner: self.owner().clone(),
            base,
            binder: (),
        }
    }
    fn with_binder(&self, binder: types::UnitBinder<'tcx>) -> StateWithBinder<'tcx> {
        State {
            base: self.base(),
            owner: self.owner().clone(),
            binder,
        }
    }
}
impl<'tcx, T: BaseState<'tcx> + HasOwner> UnderOwnerState<'tcx> for T {}

/// State of anything below a binder.
pub trait UnderBinderState<'tcx> = UnderOwnerState<'tcx> + HasBinder<'tcx>;

pub trait WithGlobalCacheExt<'tcx>: BaseState<'tcx> {
    /// Access the global cache. You must not call `sinto` within this function as this will likely
    /// result in `BorrowMut` panics.
    fn with_global_cache<T>(&self, f: impl FnOnce(&mut GlobalCache<'tcx>) -> T) -> T {
        let base = self.base();
        let mut cache = base.cache.borrow_mut();
        f(&mut cache)
    }
    /// Access the cache for a given item. You must not call `sinto` within this function as this
    /// will likely result in `BorrowMut` panics.
    fn with_item_cache<T>(&self, def_id: &DefId, f: impl FnOnce(&mut ItemCache<'tcx>) -> T) -> T {
        self.with_global_cache(|cache| f(cache.per_item.entry(def_id.clone()).or_default()))
    }
}
impl<'tcx, S: BaseState<'tcx>> WithGlobalCacheExt<'tcx> for S {}

pub trait WithItemCacheExt<'tcx>: UnderOwnerState<'tcx> {
    /// Access the cache for the current item. You must not call `sinto` within this function as
    /// this will likely result in `BorrowMut` panics.
    fn with_cache<T>(&self, f: impl FnOnce(&mut ItemCache<'tcx>) -> T) -> T {
        self.with_item_cache(&self.owner(), f)
    }
    fn with_predicate_searcher<T>(
        &self,
        f: impl FnOnce(&mut PredicateSearcher<'tcx>, &StateWithBase<'tcx>) -> T,
    ) -> T {
        let s = self;
        let base = s.base();
        let owner = s.owner();
        let base_state = s.base_state();
        let mut predicate_searcher = base.elab_ctx.predicate_searcher_for(&base_state, owner);
        f(&mut predicate_searcher, &base_state)
    }
}
impl<'tcx, S: UnderOwnerState<'tcx>> WithItemCacheExt<'tcx> for S {}
