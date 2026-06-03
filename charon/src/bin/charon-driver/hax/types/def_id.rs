//! This module contains the type definition for `DefId` and the types
//! `DefId` depends on.
//!
//! This is purposely a very small isolated module:
//! `hax-engine-names-extract` uses those types, but we don't want
//! `hax-engine-names-extract` to have a build dependency on the whole
//! frontend, that double the build times for the Rust part of hax.

use crate::hax::AdtInto;
use crate::hax::prelude::*;
use charon_lib::ast::HashConsed;

use itertools::Itertools;
pub use rustc_middle::mir::Promoted as PromotedId;
use rustc_span::DUMMY_SP;
use {rustc_hir as hir, rustc_hir::def_id::DefId as RDefId, rustc_middle::ty};

sinto_reexport!(hir::Safety);
sinto_reexport!(hir::Mutability);
sinto_reexport!(hir::def::CtorKind);
sinto_reexport!(hir::def::MacroKinds);
sinto_reexport!(hir::def::CtorOf);
sinto_reexport!(rustc_span::symbol::Symbol);
sinto_reexport!(rustc_span::symbol::ByteSymbol);

/// Reflects [`rustc_hir::def::DefKind`]
#[derive(AdtInto)]
#[args(<S>, from: rustc_hir::def::DefKind, state: S as tcx)]
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum DefKind {
    Mod,
    Struct,
    Union,
    Enum,
    Variant,
    Trait,
    TyAlias,
    ForeignTy,
    TraitAlias,
    AssocTy,
    TyParam,
    Fn,
    Const {
        is_type_const: bool,
    },
    ConstParam,
    Static {
        safety: Safety,
        mutability: Mutability,
        nested: bool,
    },
    Ctor(CtorOf, CtorKind),
    AssocFn,
    AssocConst {
        is_type_const: bool,
    },
    Macro(MacroKinds),
    ExternCrate,
    Use,
    ForeignMod,
    AnonConst,
    InlineConst,
    #[disable_mapping]
    /// Added by hax: promoted constants don't have def_ids in rustc but they do in hax.
    PromotedConst,
    OpaqueTy,
    Field,
    LifetimeParam,
    GlobalAsm,
    Impl {
        of_trait: bool,
    },
    Closure,
    SyntheticCoroutineBody,
}

/// The crate name under which synthetic items are exported under.
const SYNTHETIC_CRATE_NAME: &str = "<synthetic>";

/// Reflects [`rustc_hir::def_id::DefId`], augmented to also give ids to promoted constants (which
/// have their own ad-hoc numbering scheme in rustc for now).
#[derive(Clone, PartialEq, Eq)]
pub struct DefId {
    pub(crate) contents: HashConsed<DefIdContents>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct DefIdContents {
    pub base: DefIdBase,
    /// The kind of definition this `DefId` points to.
    pub kind: crate::hax::DefKind,
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub enum DefIdBase {
    Real(RDefId),
    Promoted(RDefId, PromotedId),
    /// This represents the context made of the trait impl generics plus the associated item
    /// generics declared in the trait. We use that context to trait solve the mapping from
    /// declared method generics to implemented method generics.
    ImplAssocItem(VirtualImplAssocItem),
    /// A completely fictitious item, we use this for arrays, slices and tuples to make
    /// monomorphization and other shenanigans easier. The contained DefId is created using
    /// `create_def`.
    /// FIXME: remove that DefId, it causes ICEs if we try to go to codegen/rlib generation.
    Synthetic(SyntheticItem, RDefId),
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub struct VirtualImplAssocItem {
    /// The trait impl.
    pub trait_impl_id: RDefId,
    /// The item declaration.
    pub item_decl_id: RDefId,
    /// The item implementation.
    pub item_impl_id: RDefId,
}

impl VirtualImplAssocItem {
    pub fn new(trait_impl_id: RDefId, item_decl_id: RDefId, item_impl_id: RDefId) -> Self {
        Self {
            trait_impl_id,
            item_decl_id,
            item_impl_id,
        }
    }

    /// Arguments just for the item itself (works for both decl and impl), valid in the virtual
    /// item context.
    fn own_args<'tcx>(&self, s: &impl BaseState<'tcx>) -> Vec<ty::GenericArg<'tcx>> {
        let tcx = s.base().tcx;
        DefId::make_assoc_item_impl(s, *self)
            .generics_of(s)
            .own_params
            .iter()
            .map(|param| tcx.mk_param_from_def(param))
            .collect()
    }

    /// Construct generic args for the item declaration, valid in the virtual item context.
    pub fn args_for_item_decl<'tcx>(
        &self,
        s: &impl BaseState<'tcx>,
        trait_args: ty::GenericArgsRef<'tcx>,
    ) -> ty::GenericArgsRef<'tcx> {
        let tcx = s.base().tcx;
        tcx.mk_args_from_iter(trait_args.iter().chain(self.own_args(s)))
    }

    /// Construct generic args for the item implementation, valid in the virtual item context.
    pub fn args_for_item_impl<'tcx>(
        &self,
        s: &impl BaseState<'tcx>,
        impl_args: ty::GenericArgsRef<'tcx>,
    ) -> ty::GenericArgsRef<'tcx> {
        let tcx = s.base().tcx;
        tcx.mk_args_from_iter(impl_args.iter().chain(self.own_args(s)))
    }

    /// Construct generic args for the item declaration, valid in the virtual item context.
    pub fn identity_args_for_item_decl<'tcx>(
        &self,
        s: &impl BaseState<'tcx>,
    ) -> ty::GenericArgsRef<'tcx> {
        let tcx = s.base().tcx;
        let impl_trait_ref = tcx
            .impl_trait_ref(self.trait_impl_id)
            .instantiate_identity()
            .skip_normalization();
        self.args_for_item_decl(s, impl_trait_ref.args)
    }
}

impl DefIdContents {
    pub fn make_def_id<'tcx, S: BaseState<'tcx>>(self, _s: &S) -> DefId {
        let contents = HashConsed::new(self);
        DefId { contents }
    }
}

impl DefId {
    /// The rustc def_id corresponding to this item, if there is one. Promoted constants don't have
    /// a rustc def_id.
    pub fn as_real_def_id(&self) -> Option<RDefId> {
        match self.base {
            DefIdBase::Real(did) => Some(did),
            _ => None,
        }
    }
    /// The rustc def_id of this item. Panics if this is not a real rustc item.
    pub fn real_rust_def_id(&self) -> RDefId {
        self.as_real_def_id().unwrap()
    }
    /// The def_id of this item or its parent if this is a promoted constant.
    pub fn as_real_or_promoted(&self) -> Option<RDefId> {
        match self.base {
            DefIdBase::Real(did) | DefIdBase::Promoted(did, ..) => Some(did),
            _ => None,
        }
    }
    /// The def_id of this item, or its parent if this is a promoted constant, or a made-up `DefId`
    /// for synthetic items.
    pub fn as_real_promoted_or_synthetic(&self) -> RDefId {
        match self.base {
            DefIdBase::Real(did) | DefIdBase::Promoted(did, ..) | DefIdBase::Synthetic(.., did) => {
                did
            }
            DefIdBase::ImplAssocItem(_) => {
                panic!("expected real, promoted, or synthetic def id, got {self:?}")
            }
        }
    }
    pub fn promoted_id(&self) -> Option<PromotedId> {
        match self.base {
            DefIdBase::Promoted(_, promoted) => Some(promoted),
            _ => None,
        }
    }
    /// Returns the [`SyntheticItem`] encoded by a [rustc `DefId`](RDefId), if
    /// any.
    ///
    /// Note that this method relies on rustc indexes, which are session
    /// specific. See [`Self`] documentation.
    pub fn as_synthetic<'tcx>(&self, _s: &impl BaseState<'tcx>) -> Option<SyntheticItem> {
        match self.base {
            DefIdBase::Synthetic(v, _) => Some(v),
            _ => None,
        }
    }

    pub fn is_local(&self) -> bool {
        match self.base {
            DefIdBase::Real(did) | DefIdBase::Promoted(did, ..) | DefIdBase::Synthetic(.., did) => {
                did.is_local()
            }
            DefIdBase::ImplAssocItem(id) => id.trait_impl_id.is_local(),
        }
    }
    pub fn is_typeck_child<'tcx>(&self, s: &impl BaseState<'tcx>) -> bool {
        match self.base {
            DefIdBase::Real(did) => s.base().tcx.is_typeck_child(did),
            _ => false,
        }
    }

    fn make<'tcx, S: BaseState<'tcx>>(s: &S, def_id: RDefId) -> Self {
        let base = match s.with_global_cache(|c| c.reverse_synthetic_map.get(&def_id).copied()) {
            None => DefIdBase::Real(def_id),
            Some(synthetic) => return Self::make_synthetic(s, synthetic, def_id),
        };
        let tcx = s.base().tcx;
        let contents = DefIdContents {
            base,
            kind: get_def_kind(tcx, def_id).sinto(s),
        };
        contents.make_def_id(s)
    }

    pub fn make_synthetic<'tcx, S: BaseState<'tcx>>(
        s: &S,
        synthetic: SyntheticItem,
        def_id: RDefId,
    ) -> Self {
        let contents = DefIdContents {
            base: DefIdBase::Synthetic(synthetic, def_id),
            kind: DefKind::Struct,
        };
        contents.make_def_id(s)
    }

    /// Construct a hax `DefId` for the nth promoted constant of the current item. That `DefId` has
    /// no corresponding rustc `DefId`.
    pub fn make_promoted_child<'tcx, S: BaseState<'tcx>>(
        &self,
        s: &S,
        promoted_id: PromotedId,
    ) -> Self {
        let contents = DefIdContents {
            base: DefIdBase::Promoted(self.real_rust_def_id(), promoted_id),
            kind: DefKind::PromotedConst,
        };
        contents.make_def_id(s)
    }

    pub fn make_assoc_item_impl<'tcx, S: BaseState<'tcx>>(
        s: &S,
        vitem: VirtualImplAssocItem,
    ) -> Self {
        let tcx = s.base().tcx;
        let contents = DefIdContents {
            base: DefIdBase::ImplAssocItem(vitem),
            kind: get_def_kind(tcx, vitem.item_decl_id).sinto(s),
        };
        contents.make_def_id(s)
    }
}

impl DefId {
    fn crate_name_and_disambig<'tcx>(&self, s: &impl BaseState<'tcx>) -> (Symbol, u32) {
        let tcx = s.base().tcx;
        match self.base {
            DefIdBase::Real(def_id)
            | DefIdBase::Promoted(def_id, ..)
            | DefIdBase::ImplAssocItem(VirtualImplAssocItem {
                trait_impl_id: def_id,
                ..
            }) => s.with_global_cache(|cache| cache.crate_name(tcx, def_id.krate)),
            DefIdBase::Synthetic(..) => (Symbol::intern(SYNTHETIC_CRATE_NAME), 0),
        }
    }

    pub fn crate_name<'tcx>(&self, s: &impl BaseState<'tcx>) -> Symbol {
        self.crate_name_and_disambig(s).0
    }

    /// Get the span of the definition of this item. This is the span used in diagnostics when
    /// referring to the item.
    pub fn def_span<'tcx>(&self, s: &impl BaseState<'tcx>) -> Span {
        use DefKind::*;
        let tcx = s.base().tcx;
        match self.base {
            DefIdBase::Real(def_id) | DefIdBase::Promoted(def_id, ..) => {
                if let ForeignMod = &self.kind {
                    // This kind causes `def_span` to panic.
                    rustc_span::DUMMY_SP
                } else if let Some(ldid) = def_id.as_local()
                    && let hir_id = tcx.local_def_id_to_hir_id(ldid)
                    && matches!(tcx.hir_node(hir_id), rustc_hir::Node::Synthetic)
                {
                    // This kind causes `def_span` to panic.
                    rustc_span::DUMMY_SP
                } else {
                    tcx.def_span(def_id)
                }
            }
            DefIdBase::ImplAssocItem(id) => tcx.def_span(id.item_impl_id),
            DefIdBase::Synthetic(..) => rustc_span::DUMMY_SP,
        }
        .sinto(s)
    }

    /// The `PathItem` corresponding to this item.
    pub fn path_item<'tcx>(&self, s: &impl BaseState<'tcx>) -> DisambiguatedDefPathItem {
        match self.base {
            DefIdBase::Real(def_id) => {
                let tcx = s.base().tcx;
                // Set the def_id so the `CrateRoot` path item can fetch the crate name.
                let s = &s.with_hax_owner(self);
                tcx.def_path(def_id)
                    .data
                    .last()
                    .map(|x| x.sinto(s))
                    .unwrap_or_else(|| {
                        let (name, disambiguator) = self.crate_name_and_disambig(s);
                        DisambiguatedDefPathItem {
                            disambiguator,
                            data: DefPathItem::CrateRoot { name },
                        }
                    })
            }
            DefIdBase::Promoted(_, id) => DisambiguatedDefPathItem {
                data: DefPathItem::PromotedConst,
                // Reuse the promoted id as disambiguator, like for inline consts.
                disambiguator: id.as_u32(),
            },
            DefIdBase::ImplAssocItem(id) => {
                let s = &s.with_hax_owner(self);
                s.base()
                    .tcx
                    .def_path(id.item_decl_id)
                    .data
                    .last()
                    .map(|x| x.sinto(s))
                    .unwrap()
            }
            DefIdBase::Synthetic(synthetic, ..) => DisambiguatedDefPathItem {
                disambiguator: 0,
                data: DefPathItem::TypeNs(Symbol::intern(&synthetic.name())),
            },
        }
    }

    pub fn parent<'tcx>(&self, s: &impl BaseState<'tcx>) -> Option<DefId> {
        match self.base {
            DefIdBase::Real(def_id) => s.tcx().opt_parent(def_id),
            DefIdBase::Promoted(def_id, _) => Some(def_id),
            DefIdBase::ImplAssocItem(id) => Some(id.trait_impl_id),
            DefIdBase::Synthetic(..) => Some(rustc_span::def_id::CRATE_DEF_ID.to_def_id()),
        }
        .sinto(s)
    }
}

impl DefId {
    pub fn can_have_generics<'tcx>(&self, s: &impl BaseState<'tcx>) -> bool {
        let tcx = s.base().tcx;
        match self.base {
            DefIdBase::Real(def_id)
            | DefIdBase::Promoted(def_id, ..)
            | DefIdBase::ImplAssocItem(VirtualImplAssocItem {
                item_decl_id: def_id,
                ..
            })
            | DefIdBase::Synthetic(.., def_id) => can_have_generics(tcx, def_id),
        }
    }

    pub fn generics_of<'tcx>(&self, s: &impl BaseState<'tcx>) -> &'tcx ty::Generics {
        let tcx = s.base().tcx;
        match self.base {
            DefIdBase::Real(def_id) | DefIdBase::Synthetic(.., def_id) => tcx.generics_of(def_id),
            DefIdBase::Promoted(def_id, ..) => s.with_item_cache(self, |cache| {
                if let Some(generics) = cache.virtual_generics {
                    return generics;
                }
                let generics = Box::leak(Box::new(ty::Generics {
                    parent: Some(def_id),
                    parent_count: tcx.generics_of(def_id).count(),
                    own_params: Default::default(),
                    param_def_id_to_index: Default::default(),
                    has_self: false,
                    has_late_bound_regions: None,
                }));
                cache.virtual_generics = Some(generics);
                generics
            }),
            DefIdBase::ImplAssocItem(id) => s.with_item_cache(self, |cache| {
                if let Some(generics) = cache.virtual_generics {
                    return generics;
                }
                // We build a custom environment here.
                let item_id = id.item_impl_id;
                let decl_generics = tcx.generics_of(item_id);
                let parent_count = tcx.generics_of(id.trait_impl_id).count();
                let own_params = tcx
                    .generics_of(id.item_decl_id)
                    .own_params
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(i, mut param)| {
                        param.index = parent_count as u32 + i as u32;
                        param
                    })
                    .collect_vec();
                let param_def_id_to_index = own_params
                    .iter()
                    .map(|param| (param.def_id, param.index))
                    .collect();
                let generics = Box::leak(Box::new(ty::Generics {
                    parent: Some(id.trait_impl_id),
                    parent_count,
                    own_params,
                    param_def_id_to_index,
                    has_self: decl_generics.has_self,
                    has_late_bound_regions: decl_generics.has_late_bound_regions,
                }));
                cache.virtual_generics = Some(generics);
                generics
            }),
        }
    }

    pub fn identity_args<'tcx>(&self, s: &impl BaseState<'tcx>) -> ty::GenericArgsRef<'tcx> {
        let tcx = s.base().tcx;
        match self.base {
            DefIdBase::Real(def_id)
            | DefIdBase::Promoted(def_id, ..)
            | DefIdBase::Synthetic(.., def_id) => {
                if can_have_generics(tcx, def_id) {
                    ty::GenericArgs::identity_for_item(tcx, def_id)
                } else {
                    ty::GenericArgsRef::default()
                }
            }
            DefIdBase::ImplAssocItem(_) => panic!(
                "virtual trait impl associated items do not have a \
                sensible `identity_args`. consider `identity_args_for_item_decl`"
            ),
        }
    }

    pub fn param_env<'tcx>(&self, s: &impl BaseState<'tcx>) -> ty::ParamEnv<'tcx> {
        let tcx = s.base().tcx;
        match self.base {
            DefIdBase::ImplAssocItem(id) => {
                let item_args = id.identity_args_for_item_decl(s);
                let impl_predicates = tcx.param_env(id.trait_impl_id).caller_bounds().iter();
                let item_predicates = tcx
                    .predicates_of(id.item_decl_id)
                    .instantiate_own(tcx, item_args)
                    .map(|(predicate, _)| predicate.skip_normalization());
                param_env_from_clauses(tcx, impl_predicates.chain(item_predicates))
            }
            DefIdBase::Real(def_id)
            | DefIdBase::Promoted(def_id, ..)
            | DefIdBase::Synthetic(.., def_id) => {
                if can_have_generics(tcx, def_id) {
                    tcx.param_env(def_id)
                } else {
                    ty::ParamEnv::empty()
                }
            }
        }
    }

    pub fn typing_env<'tcx>(&self, s: &impl BaseState<'tcx>) -> ty::TypingEnv<'tcx> {
        ty::TypingEnv::new(self.param_env(s), ty::TypingMode::PostAnalysis)
    }

    pub fn required_predicates<'tcx, S: BaseState<'tcx>>(&self, s: &S) -> ItemPredicates<'tcx> {
        match self.base {
            DefIdBase::ImplAssocItem(id) => {
                let tcx = s.base().tcx;
                let item_args = id.identity_args_for_item_decl(s);
                let mut predicates = ItemPredicates::required(s.base().elab_ctx, id.item_decl_id);
                if matches!(self.kind, DefKind::AssocFn) {
                    predicates
                        .predicates
                        .retain(|predicate| !matches!(predicate.id, ItemPredicateId::TraitSelf));
                }
                predicates.instantiate(tcx, item_args)
            }
            DefIdBase::Real(def_id) | DefIdBase::Synthetic(.., def_id) => {
                ItemPredicates::required(s.base().elab_ctx, def_id)
            }
            DefIdBase::Promoted(..) => ItemPredicates::new_unmapped(DUMMY_SP, []),
        }
    }

    pub fn type_of<'tcx, S: BaseState<'tcx>>(&self, s: &S) -> ty::EarlyBinder<'tcx, ty::Ty<'tcx>> {
        let tcx: ty::TyCtxt<'tcx> = s.base().tcx;
        match self.base {
            DefIdBase::Real(def_id)
            | DefIdBase::Promoted(def_id, ..)
            | DefIdBase::Synthetic(.., def_id) => tcx.type_of(def_id),
            DefIdBase::ImplAssocItem(id) => tcx.type_of(id.item_decl_id),
        }
    }
}

impl DefId {
    /// Gets the visibility (`pub` or not) of the definition. Returns `None` for defs that don't have a
    /// meaningful visibility.
    pub fn visibility<'tcx>(&self, tcx: ty::TyCtxt<'tcx>) -> Option<bool> {
        use DefKind::*;
        match self.kind {
            AssocConst { .. }
            | AssocFn
            | Const { .. }
            | Enum
            | Field
            | Fn
            | ForeignTy
            | Macro { .. }
            | Mod
            | Static { .. }
            | Struct
            | Trait
            | TraitAlias
            | TyAlias { .. }
            | Union
            | Use
            | Variant => {
                let def_id = self.as_real_def_id()?;
                Some(tcx.visibility(def_id).is_public())
            }
            // These kinds don't have visibility modifiers (which would cause `visibility` to panic).
            AnonConst
            | AssocTy
            | Closure
            | ConstParam
            | Ctor { .. }
            | ExternCrate
            | ForeignMod
            | GlobalAsm
            | Impl { .. }
            | InlineConst
            | PromotedConst
            | LifetimeParam
            | OpaqueTy
            | SyntheticCoroutineBody
            | TyParam => None,
        }
    }

    /// Gets the attributes of the definition.
    pub fn attrs<'tcx>(&self, tcx: ty::TyCtxt<'tcx>) -> &'tcx [rustc_hir::Attribute] {
        use DefKind::*;
        match self.kind {
            // These kinds cause `get_attrs` to panic.
            ConstParam | LifetimeParam | TyParam | ForeignMod | InlineConst => &[],
            _ => {
                if let Some(def_id) = self.as_real_def_id() {
                    if let Some(ldid) = def_id.as_local() {
                        tcx.hir_attrs(tcx.local_def_id_to_hir_id(ldid))
                    } else {
                        tcx.attrs_for_def(def_id)
                    }
                } else {
                    &[]
                }
            }
        }
    }
}

impl std::ops::Deref for DefId {
    type Target = DefIdContents;
    fn deref(&self) -> &Self::Target {
        &self.contents
    }
}

impl std::fmt::Debug for DefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.base {
            DefIdBase::Real(def_id) => write!(f, "{def_id:?}"),
            DefIdBase::Promoted(def_id, promoted) => {
                write!(f, "{def_id:?}::promoted#{}", promoted.as_u32())
            }
            DefIdBase::Synthetic(item, _) => write!(f, "{}", item.name()),
            DefIdBase::ImplAssocItem(id) => {
                write!(f, "{:?}::{:?}", id.trait_impl_id, id.item_decl_id)
            }
        }
    }
}

impl std::hash::Hash for DefId {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.base.hash(state);
    }
}

/// Gets the kind of the definition. Can't use `def_kind` directly because this crashes on the
/// crate root.
pub(crate) fn get_def_kind<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: RDefId) -> hir::def::DefKind {
    if def_id == rustc_span::def_id::CRATE_DEF_ID.to_def_id() {
        // Horrible hack: without this, `def_kind` crashes on the crate root. Presumably some table
        // isn't properly initialized otherwise.
        let _ = tcx.def_span(def_id);
    };
    tcx.def_kind(def_id)
}

impl<'s, S: BaseState<'s>> SInto<S, DefId> for RDefId {
    fn sinto(&self, s: &S) -> DefId {
        if let Some(def_id) = s.with_global_cache(|cache| cache.def_ids.get(self).cloned()) {
            return def_id;
        }
        let def_id = DefId::make(s, *self);
        s.with_global_cache(|cache| {
            cache.def_ids.insert(*self, def_id.clone());
        });
        def_id
    }
}

/// Reflects [`rustc_hir::definitions::DefPathData`]

#[derive(Clone, Debug, Hash, PartialEq, Eq, AdtInto)]
#[args(<'ctx, S: UnderOwnerState<'ctx>>, from: rustc_hir::definitions::DefPathData, state: S as s)]
pub enum DefPathItem {
    CrateRoot {
        #[value(s.base().tcx.crate_name(s.owner_id().krate).sinto(s))]
        name: Symbol,
    },
    Impl,
    ForeignMod,
    Use,
    GlobalAsm,
    TypeNs(Symbol),
    ValueNs(Symbol),
    MacroNs(Symbol),
    LifetimeNs(Symbol),
    Closure,
    Ctor,
    AnonConst,
    #[disable_mapping]
    PromotedConst,
    OpaqueTy,
    OpaqueLifetime(Symbol),
    AnonAssocTy(Symbol),
    SyntheticCoroutineBody,
    NestedStatic,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, AdtInto)]
#[args(<'a, S: UnderOwnerState<'a>>, from: rustc_hir::definitions::DisambiguatedDefPathData, state: S as s)]
/// Reflects [`rustc_hir::definitions::DisambiguatedDefPathData`]
pub struct DisambiguatedDefPathItem {
    pub data: DefPathItem,
    pub disambiguator: u32,
}
