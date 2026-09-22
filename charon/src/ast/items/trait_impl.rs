use crate::ast::*;
use crate::ids::IndexVec;
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use macros::EnumAsGetters;
use macros::EnumIsA;
use serde_state::DeserializeState;
use serde_state::SerializeState;

/// A trait **implementation**.
///
/// For instance:
/// ```text
/// impl Foo for List {
///   type Bar = ...
///
///   fn baz(...) { ... }
/// }
/// ```
#[derive(Debug, Clone)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct TraitImpl {
    pub def_id: TraitImplId,
    pub item_meta: ItemMeta,
    pub src: TraitImplSource,
    /// The information about the implemented trait.
    /// Note that this contains the instantiation of the "parent"
    /// clauses.
    pub impl_trait: TraitDeclRef,
    pub generics: GenericParams,
    /// The trait references for the parent clauses (see [TraitDecl]).
    pub implied_trait_refs: IndexVec<TraitClauseId, TraitRef>,
    /// The implemented associated constants.
    pub consts: IndexMap<AssocConstId, GlobalDeclRef>,
    /// The implemented associated types.
    pub types: IndexMap<AssocTypeId, Binder<TraitAssocTyImpl>>,
    /// The implemented methods
    pub methods: IndexMap<TraitMethodId, Binder<FunDeclRef>>,
    /// The virtual table instance for this trait implementation.
    pub vtable: VTableDecl,
}

/// The value of a trait associated type.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct TraitAssocTyImpl {
    pub value: Ty,
    /// This matches the corresponding vector in `TraitAssocTy`. In the same way, this is empty
    /// after the `lift_associated_item_clauses` pass.
    pub implied_trait_refs: IndexVec<TraitClauseId, TraitRef>,
}

/// Where the impl comes from.
#[derive(Debug, Clone)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_suffix("TraitImpl"))]
pub enum TraitImplSource {
    /// A regular trait implementation.
    Normal,
    /// The blanket implementation generated for a trait alias.
    TraitAlias,
    /// An implementation of one of the `Fn*` traits, generated for a closure.
    Closure {
        #[serde_state(stateless)]
        kind: ClosureKind,
    },
    /// The `Destruct` implementation generated for an ADT or closure.
    Destruct,
}

/// The virtual table instance for a trait implementation.
#[derive(Debug, Clone)]
#[derive(EnumIsA, EnumAsGetters)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub enum VTableDecl {
    /// The trait is not dyn-compatible, so no vtable exists.
    NotDynCompatible,
    /// The trait is dyn-compatible, but we have not computed a vtable for it, as it is not used.
    Lazy,
    /// The trait is dyn-compatible, and we have computed a vtable for it.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("VTableInstance"))]
    VTable(GlobalDeclRef),
    /// We don't support computing a vtable for this impl; the string explains why.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("UnknownVTable"))]
    Unknown(String),
}

impl TraitImpl {
    pub fn methods(&self) -> impl Iterator<Item = &Binder<FunDeclRef>> {
        self.methods.iter()
    }
}
