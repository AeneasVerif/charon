use crate::hax::prelude::*;

use rustc_data_structures::intern::Interned;
use rustc_middle::ty;
use rustc_span::def_id::DefId as RDefId;

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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ItemRef<'tcx> {
    pub(crate) contents: Interned<'tcx, ItemRefContents<'tcx>>,
}

// The rustc arguments are immutable interned data.
impl std::panic::RefUnwindSafe for ItemRef<'_> {}
impl std::panic::UnwindSafe for ItemRef<'_> {}

/// Contents of `ItemRef`.
#[derive(AdtInto)]
#[args(< S: UnderOwnerState<'tcx>>, from: rustc_trait_elaboration::ItemRef<'tcx, DefId>, state: S as s)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ItemRefContents<'tcx> {
    /// The item being refered to.
    #[value(self.def_id.clone())]
    pub def_id: DefId,
    /// Keep the original arguments. Different rustc arguments can have the same translated
    /// generics, so we must keep the args here if we want to be able to recover them.
    #[value(self.generics())]
    rustc_args: ty::GenericArgsRef<'tcx>,
    /// The generics passed to the item. If `in_trait` is `Some`, these are only the generics of
    /// the method/type/const itself; generics for the traits are available in
    /// `in_trait.unwrap().trait`.
    #[value(self.assoc_generics().sinto(s))]
    pub generic_args: Vec<GenericArg<'tcx>>,
    /// Witnesses of the trait clauses required by the item, e.g. `T: Sized` for `Option<T>` or `B:
    /// ToOwned` for `Cow<'a, B>`. Same as above, for associated items this only includes clauses
    /// for the item itself.
    #[value(self.assoc_trait_proofs().sinto(s))]
    pub trait_proofs: Vec<TraitProof<'tcx>>,
    /// If we're referring to a trait associated item, this gives the trait clause/impl we're
    /// referring to.
    #[value(self.in_trait.as_ref().map(|(x, _)| x).sinto(s))]
    pub in_trait: Option<TraitProof<'tcx>>,
    /// Whether this contains any reference to a type/lifetime/const parameter.
    #[value(self.has_param)]
    pub has_param: bool,
    /// Whether this contains any reference to a type/const parameter.
    #[value(self.has_non_lt_param)]
    pub has_non_lt_param: bool,
    /// Whether we resolved this to an impl item that a more specialized impl may override for
    /// some instantiations of the generics. In that case this reference may be wrong.
    #[value(self.may_be_further_specialized)]
    pub may_be_further_specialized: bool,
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ItemRef<'tcx>>
    for rustc_trait_elaboration::ItemRef<'tcx, DefId>
{
    fn sinto(&self, s: &S) -> ItemRef<'tcx> {
        let content: ItemRefContents = self.sinto(s);
        content.intern(s)
    }
}

impl<'tcx> ItemRefContents<'tcx> {
    fn intern(self, s: &impl BaseState<'tcx>) -> ItemRef<'tcx> {
        ItemRef {
            contents: s.base().item_ref_interner.intern(self),
        }
    }
}

impl<'tcx> ItemRef<'tcx> {
    /// The main way to obtain an `ItemRef`: from a `def_id` and generics.
    pub fn translate<S: UnderOwnerState<'tcx>>(
        s: &S,
        def_id: RDefId,
        generics: ty::GenericArgsRef<'tcx>,
    ) -> ItemRef<'tcx> {
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
    pub fn translate_from_hax_def_id<S: UnderOwnerState<'tcx>>(
        s: &S,
        hax_def_id: DefId,
        generics: ty::GenericArgsRef<'tcx>,
    ) -> ItemRef<'tcx> {
        Self::translate_from_hax_def_id_maybe_resolve(
            s,
            hax_def_id,
            generics,
            AssocItemResolution::ImplItem,
        )
    }

    pub fn translate_projection<S: UnderOwnerState<'tcx>>(
        s: &S,
        def_id: RDefId,
        generics: ty::GenericArgsRef<'tcx>,
    ) -> ItemRef<'tcx> {
        let hax_def_id = def_id.sinto(s);
        Self::translate_from_hax_def_id_maybe_resolve(
            s,
            hax_def_id,
            generics,
            AssocItemResolution::TraitProof,
        )
    }

    pub fn translate_from_hax_def_id_maybe_resolve<S: UnderOwnerState<'tcx>>(
        s: &S,
        hax_def_id: DefId,
        generics: ty::GenericArgsRef<'tcx>,
        assoc_item_resolution: AssocItemResolution,
    ) -> ItemRef<'tcx> {
        let key = (hax_def_id.clone(), generics, assoc_item_resolution);
        if let Some(item) = s.with_cache(|cache| cache.item_refs.get(&key).cloned()) {
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

        let content: ItemRefContents<'tcx> = item_ref.sinto(s);
        let item = content.intern(s);
        s.with_cache(|cache| {
            cache.item_refs.insert(key, item.clone());
        });
        item
    }

    /// Construct an `ItemRef` for items that can't have generics (e.g. modules).
    pub fn dummy_without_generics<S: BaseState<'tcx>>(s: &S, def_id: DefId) -> ItemRef<'tcx> {
        let content = ItemRefContents {
            def_id,
            rustc_args: Default::default(),
            generic_args: Default::default(),
            trait_proofs: Default::default(),
            in_trait: Default::default(),
            has_param: false,
            has_non_lt_param: false,
            may_be_further_specialized: false,
        };
        content.intern(s)
    }

    /// For an `ItemRef` that refers to a trait, this returns values for each of the non-gat
    /// associated types of this trait and its parents, in a fixed order.
    pub fn trait_associated_types<S: UnderOwnerState<'tcx>>(&self, s: &S) -> Vec<Ty<'tcx>> {
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
    pub fn erase<S: UnderOwnerState<'tcx>>(&self, s: &S) -> Self {
        let args = self.rustc_args(s);
        let args = erase_and_norm(
            s.base().tcx,
            s.typing_env(),
            ty::Unnormalized::new_wip(args),
        );
        Self::translate_from_hax_def_id(s, self.def_id.clone(), args)
    }

    /// Reconstruct this item reference with the requested associated item resolution.
    pub fn re_resolve<S: UnderOwnerState<'tcx>>(
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

    pub fn contents(&self) -> &ItemRefContents<'tcx> {
        &self.contents
    }

    /// Recover the original rustc args that generated this `ItemRef`.
    pub fn rustc_args<S: BaseState<'tcx>>(&self, _s: &S) -> ty::GenericArgsRef<'tcx> {
        self.rustc_args
    }

    /// Mutate the `DefId`, keeping the same generic args.
    pub fn mutate_def_id<S: BaseState<'tcx>>(&self, s: &S, f: impl FnOnce(&mut DefId)) -> Self {
        let mut contents = self.contents().clone();
        f(&mut contents.def_id);
        contents.intern(s)
    }

    /// Set the `DefId`, keeping the same generic args.
    pub fn with_def_id<S: BaseState<'tcx>>(&self, s: &S, def_id: &DefId) -> Self {
        self.mutate_def_id(s, |d| *d = def_id.clone())
    }

    /// The parent of this item if the item inherits the typing context from its parent (e.g. closures and methods).
    pub fn typing_parent<S: UnderOwnerState<'tcx>>(&self, s: &S) -> Option<ItemRef<'tcx>> {
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

    /// Like [`Self::typing_parent`], but includes enclosing closures and inline consts that
    /// rustc does not consider "parents" for the purposes of generic arguments. E.g. a closure has
    /// three extra inference parameters, and a nested closure does not inherit them.
    ///
    /// Also returns
    /// 1. the suffix of the arguments that was cut off, if any, and
    /// 2. the corresponding suffix of this item's unerased + instantiated identity args.
    ///
    /// These two are almost always the same, except for typeck children: these have some erased
    /// regions in their indentity args, which we will want to unify with the actual provided args
    /// in order to recover their values. The unerased identity args contain placeholder regions at
    /// these erased locations, corresponding to the `ParamEnv`'s `extra_early_regions`.
    pub fn soft_typing_parent<S: UnderOwnerState<'tcx>>(
        &self,
        s: &S,
    ) -> (
        Option<ItemRef<'tcx>>,
        ty::GenericArgsRef<'tcx>,
        ty::GenericArgsRef<'tcx>,
    ) {
        let tcx = s.tcx();
        let typing_parent = self.typing_parent(s);
        let typing_parent_count = match &typing_parent {
            Some(typing_parent) => typing_parent.rustc_args(s).len(),
            None => 0,
        };
        let args = self.rustc_args(s);
        let own_args = tcx.mk_args(&args[typing_parent_count..]);
        let (identity_args, _) = self.def_id.identity_args_with_extra_regions(s);
        let own_template = substitute(
            tcx,
            s.typing_env(),
            Some(args),
            tcx.mk_args(&identity_args[typing_parent_count..]),
        );

        let soft_parent = if self.def_id.is_typeck_child(s)
            && let Some(typing_parent) = &typing_parent
            && let Some(nesting_parent) = self.def_id.parent(s)
            && nesting_parent != typing_parent.def_id
        {
            // We construct a reference to the nesting parent. This may have _more_ arguments (e.g.
            // if we'r ea closure inside a closure). Thankfully these extra args can always be
            // recovered (modulo erased lifetimes) from the (common) typing parent's arguments.
            // We do so here, using our `DefId::identity_args`.
            let parent_args = substitute(
                s.tcx(),
                s.typing_env(),
                Some(typing_parent.rustc_args(s)),
                nesting_parent.identity_args(s),
            );
            Some(ItemRef::translate_from_hax_def_id(
                s,
                nesting_parent,
                parent_args,
            ))
        } else {
            typing_parent
        };
        (soft_parent, own_args, own_template)
    }
}

impl<'tcx> std::ops::Deref for ItemRef<'tcx> {
    type Target = ItemRefContents<'tcx>;
    fn deref(&self) -> &Self::Target {
        self.contents()
    }
}
