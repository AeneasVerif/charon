use crate::ast::*;
use crate::ids::IndexVec;
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use serde_state::DeserializeState;
use serde_state::SerializeState;

#[derive(
    Debug,
    Clone,
    Copy,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[serde_state(stateless)]
pub struct TraitItemName(pub ustr::Ustr);

generate_index_type!(TraitMethodId, "TraitMethod");
generate_index_type!(AssocTypeId, "AssocType");
generate_index_type!(AssocConstId, "AssocConst");

/// A trait **declaration**.
///
/// For instance:
/// ```text
/// trait Foo {
///   type Bar;
///
///   fn baz(...); // required method (see below)
///
///   fn test() -> bool { true } // provided method (see below)
/// }
/// ```
///
/// In case of a trait declaration, we don't include the provided methods (the methods
/// with a default implementation): they will be translated on a per-need basis. This is
/// important for two reasons:
/// - this makes the trait definitions a lot smaller (the Iterator trait
///   has *one* declared function and more than 70 provided functions)
/// - this is important for the external traits, whose provided methods
///   often use features we don't support yet
///
/// Remark:
/// In Aeneas, we still translate the provided methods on an individual basis,
/// and in such a way thay they take as input a trait instance. This means that
/// we can use default methods *but*:
/// - implementations of required methods shoudln't call default methods
/// - trait implementations shouldn't redefine required methods
///
/// The use case we have in mind is [std::iter::Iterator]: it declares one required
/// method (`next`) that should be implemented for every iterator, and defines many
/// helpers like `all`, `map`, etc. that shouldn't be re-implemented.
/// Of course, this forbids other useful use cases such as visitors implemented
/// by means of traits.
#[allow(clippy::type_complexity)]
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct TraitDecl {
    pub def_id: TraitDeclId,
    pub item_meta: ItemMeta,
    /// Distinguishes normal traits from trait aliases.
    pub src: TraitDeclSource,
    pub generics: GenericParams,
    /// The "parent" clauses: the supertraits.
    ///
    /// Supertraits are actually regular where clauses, but we decided to have
    /// a custom treatment.
    /// ```text
    /// trait Foo : Bar {
    ///             ^^^
    ///         supertrait, that we treat as a parent predicate
    /// }
    /// ```
    /// TODO: actually, as of today, we consider that all trait clauses of
    /// trait declarations are parent clauses.
    pub implied_clauses: IndexVec<TraitClauseId, TraitParam>,
    /// The associated constants declared in the trait.
    pub consts: IndexMap<AssocConstId, TraitAssocConst>,
    /// The associated types declared in the trait. The binder binds the generic parameters of the
    /// type if it is a GAT (Generic Associated Type). For a plain associated type the binder binds
    /// nothing.
    pub types: IndexMap<AssocTypeId, Binder<TraitAssocTy>>,
    /// The methods declared by the trait. The binder binds the generic parameters of the method.
    ///
    /// ```rust
    /// trait Trait<T> {
    ///   // The `Binder` for this method binds `'a` and `U`.
    ///   fn method<'a, U>(x: &'a U);
    /// }
    /// ```
    pub methods: IndexMap<TraitMethodId, Binder<TraitMethod>>,
    /// The virtual table struct for this trait, if it has one.
    /// It is guaranteed that the trait has a vtable iff it is dyn-compatible.
    pub vtable: Option<TypeDeclRef>,
}

/// An associated constant in a trait.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct TraitAssocConst {
    pub name: TraitItemName,
    #[serde_state(stateless)]
    pub attr_info: AttrInfo,
    pub ty: Ty,
    pub default: Option<GlobalDeclRef>,
}

/// An associated type in a trait.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct TraitAssocTy {
    pub name: TraitItemName,
    #[serde_state(stateless)]
    pub attr_info: AttrInfo,
    pub default: Option<TraitAssocTyImpl>,
    /// List of trait clauses that apply to this type.
    pub implied_clauses: IndexVec<TraitClauseId, TraitParam>,
}

/// A trait method.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct TraitMethod {
    pub name: TraitItemName,
    pub item_meta: ItemMeta,
    pub signature: FunSig,
    /// The default method implementation, if there is one.
    pub default: Option<FunDeclRef>,
}

/// Where the trait comes from.
#[derive(Debug, Clone, Copy, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_suffix("TraitDecl"))]
pub enum TraitDeclSource {
    /// A regular trait.
    Normal,
    /// The trait declaration coming from a trait alias.
    TraitAlias,
}

impl TraitDecl {
    pub fn methods(&self) -> impl Iterator<Item = &Binder<TraitMethod>> {
        self.methods.iter()
    }
}

impl Binder<TraitAssocTy> {
    pub fn name(&self) -> &TraitItemName {
        &self.skip_binder.name
    }
}
impl Binder<TraitMethod> {
    pub fn name(&self) -> TraitItemName {
        self.skip_binder.name
    }
}
