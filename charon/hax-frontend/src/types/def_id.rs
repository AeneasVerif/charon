//! This module contains the type definition for `DefId` and the types
//! `DefId` depends on.
//!
//! This is purposely a very small isolated module:
//! `hax-engine-names-extract` uses those types, but we don't want
//! `hax-engine-names-extract` to have a build dependency on the whole
//! frontend, that double the build times for the Rust part of hax.

use crate::AdtInto;
use crate::prelude::*;

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
    Const,
    ConstParam,
    Static {
        safety: Safety,
        mutability: Mutability,
        nested: bool,
    },
    Ctor(CtorOf, CtorKind),
    AssocFn,
    AssocConst,
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

pub use rustc_middle::mir::Promoted as PromotedId;

/// Reflects [`rustc_hir::def_id::DefId`], augmented to also give ids to promoted constants (which
/// have their own ad-hoc numbering scheme in rustc for now).
#[derive(Clone, PartialEq, Eq)]
pub struct DefId {
    pub(crate) contents: crate::id_table::hash_consing::HashConsed<DefIdContents>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct DefIdContents {
    pub parent: Option<DefId>,
    pub base: RDefId,
    pub promoted: Option<PromotedId>,
    /// The kind of definition this `DefId` points to.
    pub kind: crate::DefKind,
}

impl DefIdContents {
    pub fn make_def_id<'tcx, S: BaseState<'tcx>>(self, _s: &S) -> DefId {
        let contents = id_table::hash_consing::HashConsed::new(self);
        DefId { contents }
    }
}

/// Returns the [`SyntheticItem`] encoded by a [rustc `DefId`](RDefId), if any.
pub fn def_id_as_synthetic<'tcx>(
    def_id: RDefId,
    s: &impl BaseState<'tcx>,
) -> Option<SyntheticItem> {
    s.with_global_cache(|c| c.reverse_synthetic_map.get(&def_id).copied())
}

impl DefId {
    /// The rustc def_id corresponding to this item, if there is one. Promoted constants don't have
    /// a rustc def_id.
    pub fn as_rust_def_id(&self) -> Option<RDefId> {
        match self.promoted {
            None => Some(self.underlying_rust_def_id()),
            Some(_) => None,
        }
    }
    /// The def_id of this item or its parent if this is a promoted constant.
    pub fn underlying_rust_def_id(&self) -> RDefId {
        self.base
    }

    pub fn is_local(&self) -> bool {
        self.base.is_local()
    }
    pub fn promoted_id(&self) -> Option<PromotedId> {
        self.promoted
    }

    /// Returns the [`SyntheticItem`] encoded by a [rustc `DefId`](RDefId), if
    /// any.
    ///
    /// Note that this method relies on rustc indexes, which are session
    /// specific. See [`Self`] documentation.
    pub fn as_synthetic<'tcx>(&self, s: &impl BaseState<'tcx>) -> Option<SyntheticItem> {
        def_id_as_synthetic(self.underlying_rust_def_id(), s)
    }

    pub fn crate_name<'tcx>(&self, s: &impl BaseState<'tcx>) -> Symbol {
        let tcx = s.base().tcx;
        if def_id_as_synthetic(self.base, s).is_some() {
            Symbol::intern(SYNTHETIC_CRATE_NAME)
        } else {
            tcx.crate_name(self.base.krate)
        }
    }

    /// The `PathItem` corresponding to this item.
    pub fn path_item<'tcx>(&self, s: &impl BaseState<'tcx>) -> DisambiguatedDefPathItem {
        match self.promoted {
            Some(id) => DisambiguatedDefPathItem {
                data: DefPathItem::PromotedConst,
                // Reuse the promoted id as disambiguator, like for inline consts.
                disambiguator: id.as_u32(),
            },
            None => {
                let tcx = s.base().tcx;
                // Set the def_id so the `CrateRoot` path item can fetch the crate name.
                let state_with_id = s.with_owner_id(self.base);
                tcx.def_path(self.base)
                    .data
                    .last()
                    .map(|x| x.sinto(&state_with_id))
                    .unwrap_or_else(|| DisambiguatedDefPathItem {
                        disambiguator: 0,
                        data: DefPathItem::CrateRoot {
                            name: self.crate_name(s),
                        },
                    })
            }
        }
    }

    /// Construct a hax `DefId` for the nth promoted constant of the current item. That `DefId` has
    /// no corresponding rustc `DefId`.
    pub fn make_promoted_child<'tcx, S: BaseState<'tcx>>(
        &self,
        s: &S,
        promoted_id: PromotedId,
    ) -> Self {
        let contents = DefIdContents {
            parent: Some(self.clone()),
            base: self.base,
            promoted: Some(promoted_id),
            kind: DefKind::PromotedConst,
        };
        contents.make_def_id(s)
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
        // Use the more legible rustc debug implementation.
        write!(f, "{:?}", self.underlying_rust_def_id())?;
        if let Some(promoted) = self.promoted_id() {
            write!(f, "::promoted#{}", promoted.as_u32())?;
        }
        Ok(())
    }
}

impl std::hash::Hash for DefId {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.base.hash(state);
        self.promoted_id().hash(state);
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

/// The crate name under which synthetic items are exported under.
pub(super) const SYNTHETIC_CRATE_NAME: &str = "<synthetic>";

fn translate_def_id<'tcx, S: BaseState<'tcx>>(s: &S, def_id: RDefId) -> DefId {
    let tcx = s.base().tcx;
    let contents = DefIdContents {
        parent: tcx.opt_parent(def_id).sinto(s),
        base: def_id,
        promoted: None,
        kind: get_def_kind(tcx, def_id).sinto(s),
    };
    contents.make_def_id(s)
}

impl<'s, S: BaseState<'s>> SInto<S, DefId> for RDefId {
    fn sinto(&self, s: &S) -> DefId {
        if let Some(def_id) = s.with_item_cache(*self, |cache| cache.def_id.clone()) {
            return def_id;
        }
        let def_id = translate_def_id(s, *self);
        s.with_item_cache(*self, |cache| cache.def_id = Some(def_id.clone()));
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
    LateAnonConst,
    AnonConst,
    #[disable_mapping]
    PromotedConst,
    DesugaredAnonymousLifetime,
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
