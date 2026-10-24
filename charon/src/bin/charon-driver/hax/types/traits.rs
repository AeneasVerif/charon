use crate::hax::prelude::*;

use rustc_middle::ty;

/// Reflects [`ty::TraitRef`]
/// Contains the def_id and arguments passed to the trait. The first type argument is the `Self`
/// type. The trait proofs are the _required_ predicate for this trait; currently they are always
/// empty because we consider all trait predicates as implied.
/// `self.in_trait` is always `None` because a trait can't be associated to another one.
pub type TraitRef<'tcx> = ItemRef<'tcx>;

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, TraitRef<'tcx>> for ty::TraitRef<'tcx> {
    fn sinto(&self, s: &S) -> TraitRef<'tcx> {
        translate_item_ref(s, self.def_id, self.args)
    }
}

/// Reflects [`ty::AssocItem`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AssocItem<'tcx> {
    pub def_id: DefId,
    /// This is `None` for RPTITs.
    pub name: Option<Symbol>,
    pub kind: AssocKind,
    pub container: AssocItemContainer<'tcx>,
    /// Whether this item has a value (e.g. this is `false` for trait methods without default
    /// implementations).
    pub has_value: bool,
}

impl<'tcx> AssocItem<'tcx> {
    pub fn sfrom<S: BaseState<'tcx>>(s: &S, item: &ty::AssocItem) -> AssocItem<'tcx> {
        Self::sfrom_instantiated(s, item, None)
    }

    /// Translate an `AssocItem` and optionally instantiate it with the provided arguments.
    pub fn sfrom_instantiated<S: BaseState<'tcx>>(
        s: &S,
        item: &ty::AssocItem,
        item_args: Option<ty::GenericArgsRef<'tcx>>,
    ) -> AssocItem<'tcx> {
        let tcx = s.base().tcx;
        // We want to solve traits in the context of this item.
        let item_def_id = item.def_id.sinto(s);
        let s = &s.with_hax_owner(&item_def_id);
        let item_args = item_args.unwrap_or_else(|| item_def_id.identity_args(s));
        let container_id = item.container_id(tcx);
        let container_args = item_args.truncate_to(tcx, tcx.generics_of(container_id));
        let container = match item.container {
            ty::AssocContainer::Trait => {
                let trait_ref =
                    ty::TraitRef::new_from_args(tcx, container_id, container_args).sinto(s);
                AssocItemContainer::TraitContainer { trait_ref }
            }
            ty::AssocContainer::TraitImpl(implemented_item_id) => {
                let implemented_item_id = implemented_item_id.unwrap();
                let item = translate_item_ref(s, container_id, container_args);
                let implemented_trait_ref = tcx
                    .impl_trait_ref(container_id)
                    .instantiate(tcx, container_args);
                let implemented_trait_ref = normalize(tcx, s.typing_env(), implemented_trait_ref);
                let implemented_trait_item = {
                    let implemented_item_id = implemented_item_id.sinto(s);
                    let generics =
                        item_args.rebase_onto(tcx, container_id, implemented_trait_ref.args);
                    // Don't resolve, otherwise we'll always get the impl item id back.
                    ItemRef::translate_from_hax_def_id_maybe_resolve(
                        s,
                        implemented_item_id,
                        generics,
                        AssocItemResolution::None,
                    )
                };
                AssocItemContainer::TraitImplContainer {
                    impl_: item,
                    implemented_trait_ref: implemented_trait_ref.sinto(s),
                    implemented_trait_item,
                    overrides_default: tcx.defaultness(implemented_item_id).has_value(),
                }
            }
            ty::AssocContainer::InherentImpl => AssocItemContainer::InherentImplContainer {
                impl_id: container_id.sinto(s),
            },
        };
        let name = match item.opt_name() {
            None if let ty::AssocKind::Type { data } = item.kind
                && let ty::AssocTypeData::Rpitit(rpitit) = data =>
            {
                let (ty::ImplTraitInTraitData::Trait { fn_def_id, .. }
                | ty::ImplTraitInTraitData::Impl { fn_def_id, .. }) = rpitit;
                let fn_name = tcx.item_name(fn_def_id);
                let name = Symbol::intern(&format!("{fn_name}_ty"));
                Some(name)
            }
            opt_name => opt_name,
        };
        AssocItem {
            def_id: item.def_id.sinto(s),
            name,
            kind: item.kind.sinto(s),
            container,
            has_value: item.defaultness(tcx).has_value(),
        }
    }

    /// The `DefId` of the item being implemented.
    pub fn implemented_trait_item_id(&self) -> &DefId {
        match &self.container {
            AssocItemContainer::TraitImplContainer {
                implemented_trait_item,
                ..
            } => &implemented_trait_item.def_id,
            _ => &self.def_id,
        }
    }
}

/// Reflects [`ty::AssocKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: ty::AssocKind, state: S as _tcx)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AssocKind {
    Const { name: Symbol },
    Fn { name: Symbol, has_self: bool },
    Type { data: AssocTypeData },
}

/// Reflects [`ty::AssocTypeData`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: ty::AssocTypeData, state: S as _tcx)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AssocTypeData {
    Normal(Symbol),
    Rpitit(ImplTraitInTraitData),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AssocItemContainer<'tcx> {
    TraitContainer {
        trait_ref: TraitRef<'tcx>,
    },
    TraitImplContainer {
        /// Reference to the def_id of the impl block.
        impl_: ItemRef<'tcx>,
        /// The trait ref implemented by the impl block.
        implemented_trait_ref: TraitRef<'tcx>,
        /// The the associated item (in the trait declaration) that is being implemented.
        implemented_trait_item: ItemRef<'tcx>,
        /// Whether the corresponding trait item had a default (and therefore this one overrides
        /// it).
        overrides_default: bool,
    },
    InherentImplContainer {
        impl_id: DefId,
    },
}

/// Reflects [`ty::ImplTraitInTraitData`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: ty::ImplTraitInTraitData, state: S as _s)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ImplTraitInTraitData {
    Trait {
        fn_def_id: DefId,
        opaque_def_id: DefId,
    },
    Impl {
        fn_def_id: DefId,
    },
}
