use crate::hax::prelude::*;

use charon_lib::ast::HashConsed;
use rustc_middle::ty;
use rustc_middle::ty::TypeVisitableExt;
use rustc_span::def_id::DefId as RDefId;
use std::borrow::Cow;

/// Reference to an item, with generics. Basically any mention of an item (function, type, etc)
/// uses this.
///
/// This can refer to a top-level item or to a trait associated item. Example:
/// ```text
/// trait MyTrait<TraitType, const TraitConst: usize> {
///   fn meth<MethType>(...) {...}
/// }
/// fn example_call<TraitType, SelfType: MyTrait<TraitType, 12>>(x: SelfType) {
///   x.meth::<String>(...)
/// }
/// ```
/// Here, in the call `x.meth::<String>(...)` we will build an `ItemRef` that looks like:
/// ```text
/// ItemRef {
///     def_id = MyTrait::meth,
///     generic_args = [String],
///     trait_proofs = [<proof of `String: Sized`>],
///     in_trait = Some(<proof of `SelfType: MyTrait<TraitType, 12>`>,
/// }
/// ```
/// The `in_trait` `TraitProof` will have in its `trait` field a representation of the `SelfType:
/// MyTrait<TraitType, 12>` predicate, which looks like:
/// ```text
/// ItemRef {
///     def_id = MyTrait,
///     generic_args = [SelfType, TraitType, 12],
///     trait_proofs = [],
///     in_trait = None,
/// }
/// ```
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct ItemRef {
    pub(crate) contents: HashConsed<ItemRefContents>,
}

/// Contents of `ItemRef`.
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: rustc_trait_elaboration::ItemRef<'tcx, DefId>, state: S as s)]
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct ItemRefContents {
    /// The item being refered to.
    #[value(self.def_id.clone())]
    pub def_id: DefId,
    /// The generics passed to the item. If `in_trait` is `Some`, these are only the generics of
    /// the method/type/const itself; generics for the traits are available in
    /// `in_trait.unwrap().trait`.
    #[value(self.assoc_generics().sinto(s))]
    pub generic_args: Vec<GenericArg>,
    /// Witnesses of the trait clauses required by the item, e.g. `T: Sized` for `Option<T>` or `B:
    /// ToOwned` for `Cow<'a, B>`. Same as above, for associated items this only includes clauses
    /// for the item itself.
    #[value(Default::default())]
    trait_proofs: LazyTraitProofs,
    /// The item under which this reference was made, if the generics mention its parameters:
    /// the trait proofs may then refer to its local clauses.
    #[value(self.has_owner_param.then(|| s.owner()))]
    owner: Option<DefId>,
    /// If we're referring to a trait associated item, this gives the trait clause/impl we're
    /// referring to.
    #[value(self.in_trait.as_ref().map(|(x, _)| x).sinto(s))]
    pub in_trait: Option<TraitProof>,
    /// Whether this contains any reference to a type/lifetime/const parameter.
    #[value(self.has_param)]
    pub has_param: bool,
    /// Whether this contains any reference to a type/const parameter.
    #[value(self.has_non_lt_param)]
    pub has_non_lt_param: bool,
}

/// Trait proofs of an `ItemRef`, computed lazily
#[derive(Clone, Debug, Default)]
pub struct LazyTraitProofs(std::sync::OnceLock<Vec<TraitProof>>);
impl std::hash::Hash for LazyTraitProofs {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}
impl PartialEq for LazyTraitProofs {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl Eq for LazyTraitProofs {}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ItemRef>
    for rustc_trait_elaboration::ItemRef<'tcx, DefId>
{
    fn sinto(&self, s: &S) -> ItemRef {
        let content: ItemRefContents = self.sinto(s);
        let item = content.intern(s);
        s.with_global_cache(|cache| {
            cache
                .reverse_item_refs_map
                .insert(item.clone(), self.generics());
        });
        item
    }
}

impl ItemRefContents {
    fn intern<'tcx, S: BaseState<'tcx>>(self, _s: &S) -> ItemRef {
        let contents = HashConsed::new(self);
        ItemRef { contents }
    }
}

impl ItemRef {
    /// The main way to obtain an `ItemRef`: from a `def_id` and generics.
    pub fn translate<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        def_id: RDefId,
        generics: ty::GenericArgsRef<'tcx>,
    ) -> ItemRef {
        let hax_def_id = def_id.sinto(s);
        Self::translate_from_hax_def_id(s, hax_def_id, generics)
    }

    /// Makes a `ItemRef` from a `def_id` and generics.
    ///
    /// If `(def_id, generics)` points to a trait item that can be resolved to a specific `impl`,
    /// `translate` rewrites `def_id` to the concrete associated item from that `impl` and re-bases
    /// the generics.
    ///
    /// For instance, `<u32 as From<u8>>::from` produces a [`ItemRef`] with a [`DefId`] looking
    /// like `core::convert::num::Impl#42::from` when `resolve_impl` is `true`,
    /// `core::convert::From::from` otherwise.
    pub fn translate_from_hax_def_id<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        hax_def_id: DefId,
        generics: ty::GenericArgsRef<'tcx>,
    ) -> ItemRef {
        Self::translate_from_hax_def_id_maybe_resolve(
            s,
            hax_def_id,
            generics,
            AssocItemResolution::ImplItem,
        )
    }

    pub fn translate_projection<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        def_id: RDefId,
        generics: ty::GenericArgsRef<'tcx>,
    ) -> ItemRef {
        let hax_def_id = def_id.sinto(s);
        Self::translate_from_hax_def_id_maybe_resolve(
            s,
            hax_def_id,
            generics,
            AssocItemResolution::TraitProof,
        )
    }

    pub fn translate_from_hax_def_id_maybe_resolve<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        hax_def_id: DefId,
        generics: ty::GenericArgsRef<'tcx>,
        assoc_item_resolution: AssocItemResolution,
    ) -> ItemRef {
        let key = (hax_def_id.clone(), generics, assoc_item_resolution);
        if let Some(item) = s.with_cache(|cache| cache.item_refs.get(&key).cloned()) {
            return item;
        }

        let is_concrete = !generics.has_non_region_param() && !s.owner_has_concrete_clauses();
        if is_concrete
            && let Some(item) =
                s.with_global_cache(|cache| cache.concrete_item_refs.get(&key).cloned())
        {
            s.with_cache(|cache| {
                cache.item_refs.insert(key, item.clone());
            });
            return item;
        }

        // Don't resolve if the DefId isn't real.
        let is_real_def_id = hax_def_id.as_real_def_id().is_some();
        let assoc_item_resolution = if is_real_def_id {
            assoc_item_resolution
        } else {
            AssocItemResolution::None
        };
        let item_ref = s.with_predicate_searcher(|pred_searcher, state| {
            pred_searcher.resolve_item_reference(
                state,
                hax_def_id.clone(),
                generics,
                assoc_item_resolution,
            )
        });

        let content: ItemRefContents = item_ref.sinto(s);
        let item = content.intern(s);
        s.with_global_cache(|cache| {
            cache
                .reverse_item_refs_map
                .insert(item.clone(), item_ref.generics());
            if is_concrete {
                cache.concrete_item_refs.insert(key.clone(), item.clone());
            }
        });
        s.with_cache(|cache| {
            cache.item_refs.insert(key, item.clone());
        });
        item
    }

    /// Witnesses of the trait clauses required by the item, e.g. `T: Sized` for `Option<T>`.
    pub fn trait_proofs<'tcx, S: UnderOwnerState<'tcx>>(&self, s: &S) -> Cow<'_, [TraitProof]> {
        let resolve = |owner: &DefId| {
            let s = &s.with_hax_owner(owner);
            let args = self.rustc_args(s);
            let trait_proofs = s.with_predicate_searcher(|pred_searcher, state| {
                pred_searcher.resolve_item_assoc_trait_proofs(
                    state,
                    self.def_id.clone(),
                    args,
                    self.in_trait.is_some(),
                )
            });
            trait_proofs.sinto(s)
        };
        match &self.owner {
            // If the proofs depend on the owner, resolve them in the owner's context and cache them.
            Some(owner) => Cow::Borrowed(self.trait_proofs.0.get_or_init(|| resolve(owner))),
            // If the proofs don't depend on the owner, but the current owner has concrete clauses, resolve
            // them in the current context and don't cache them, since they may change.
            None if s.owner_has_concrete_clauses() => Cow::Owned(resolve(&s.owner())),
            // If the proofs don't depend on the owner, resolve them in the current context.
            None => Cow::Borrowed(self.trait_proofs.0.get_or_init(|| resolve(&s.owner()))),
        }
    }

    /// Construct an `ItemRef` for items that can't have generics (e.g. modules).
    pub fn dummy_without_generics<'tcx, S: BaseState<'tcx>>(s: &S, def_id: DefId) -> ItemRef {
        let content = ItemRefContents {
            def_id,
            generic_args: Default::default(),
            trait_proofs: Default::default(),
            owner: None,
            in_trait: Default::default(),
            has_param: false,
            has_non_lt_param: false,
        };
        let item = content.intern(s);
        s.with_global_cache(|cache| {
            cache
                .reverse_item_refs_map
                .insert(item.clone(), ty::GenericArgsRef::default());
        });
        item
    }

    /// For an `ItemRef` that refers to a trait, this returns values for each of the non-gat
    /// associated types of this trait and its parents, in a fixed order.
    pub fn trait_associated_types<'tcx, S: UnderOwnerState<'tcx>>(&self, s: &S) -> Vec<Ty> {
        if !matches!(self.def_id.kind, DefKind::Trait | DefKind::TraitAlias) {
            panic!("`ItemRef::trait_associated_types` expected a trait")
        }
        let tcx = s.base().tcx;
        let typing_env = s.typing_env();
        let def_id = self.def_id.real_rust_def_id();
        let generics = self.rustc_args(s);
        let tref = ty::TraitRef::new(tcx, def_id, generics);
        rustc_utils::assoc_tys_for_trait(tcx, typing_env, tref)
            .into_iter()
            .map(|alias_ty| ty::Ty::new_alias(tcx, ty::IsRigid::No, alias_ty))
            .map(|ty| normalize(tcx, typing_env, ty::Unnormalized::new(ty)))
            .map(|ty| ty.sinto(s))
            .collect()
    }

    /// Erase lifetimes from the generic arguments of this item.
    pub fn erase<'tcx, S: UnderOwnerState<'tcx>>(&self, s: &S) -> Self {
        let args = self.rustc_args(s);
        let args = erase_and_norm(
            s.base().tcx,
            s.typing_env(),
            ty::Unnormalized::new_wip(args),
        );
        Self::translate_from_hax_def_id(s, self.def_id.clone(), args)
    }

    /// Reconstruct this item reference with the requested associated item resolution.
    pub fn re_resolve<'tcx, S: UnderOwnerState<'tcx>>(
        &self,
        s: &S,
        assoc_item_resolution: AssocItemResolution,
    ) -> Self {
        Self::translate_from_hax_def_id_maybe_resolve(
            s,
            self.def_id.clone(),
            self.rustc_args(s),
            assoc_item_resolution,
        )
    }

    pub fn contents(&self) -> &ItemRefContents {
        &self.contents
    }

    /// Recover the original rustc args that generated this `ItemRef`. Will panic if the `ItemRef`
    /// was built by hand instead of using `translate_item_ref`.
    pub fn rustc_args<'tcx, S: BaseState<'tcx>>(&self, s: &S) -> ty::GenericArgsRef<'tcx> {
        s.with_global_cache(|cache| *cache.reverse_item_refs_map.get(self).unwrap())
    }

    /// Mutate the `DefId`, keeping the same generic args.
    pub fn mutate_def_id<'tcx, S: BaseState<'tcx>>(
        &self,
        s: &S,
        f: impl FnOnce(&mut DefId),
    ) -> Self {
        let args = self.rustc_args(s);
        let mut contents = self.contents().clone();
        f(&mut contents.def_id);
        contents.trait_proofs = Default::default();
        let new = contents.intern(s);
        s.with_global_cache(|cache| {
            cache.reverse_item_refs_map.insert(new.clone(), args);
        });
        new
    }

    /// Set the `DefId`, keeping the same generic args.
    pub fn with_def_id<'tcx, S: BaseState<'tcx>>(&self, s: &S, def_id: &DefId) -> Self {
        self.mutate_def_id(s, |d| *d = def_id.clone())
    }

    /// The parent of this item if the item inherits the typing context from its parent (e.g. closures and methods).
    pub fn typing_parent<'tcx, S: BaseState<'tcx>>(&self, s: &S) -> Option<ItemRef> {
        match self.def_id.kind {
            DefKind::AssocTy
            | DefKind::AssocFn
            | DefKind::AssocConst
            | DefKind::Closure
            | DefKind::AnonConst
            | DefKind::PromotedConst => {
                let tcx = s.base().tcx;
                let parent = self.def_id.generics_of(s).parent?.sinto(s);
                let parent_args = self.rustc_args(s).truncate_to(tcx, parent.generics_of(s));
                let s = &s.with_hax_owner(&self.def_id);
                Some(ItemRef::translate_from_hax_def_id(s, parent, parent_args))
            }
            DefKind::Ctor(..) | DefKind::Variant => {
                let parent = self.def_id.parent(s).unwrap();
                // The parent has the same generics as this item.
                Some(self.with_def_id(s, &parent))
            }
            _ => None,
        }
    }
}

impl std::ops::Deref for ItemRef {
    type Target = ItemRefContents;
    fn deref(&self) -> &Self::Target {
        self.contents()
    }
}
