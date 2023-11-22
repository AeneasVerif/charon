//! Definitions common to [crate::ullbc_ast] and [crate::llbc_ast]
#![allow(dead_code)]

pub use crate::expressions::*;
pub use crate::gast_utils::*;
use crate::meta::Meta;
use crate::names::Name;
pub use crate::types::GlobalDeclId;
pub use crate::types::TraitClauseId;
use crate::types::*;
pub use crate::types::{
    GenericArgs, GenericParams, TraitDeclId, TraitImplId, TraitInstanceId, TraitRef,
};
use macros::generate_index_type;
use serde::Serialize;

generate_index_type!(FunDeclId);

/// A variable
#[derive(Debug, Clone, Serialize)]
pub struct Var {
    /// Unique index identifying the variable
    pub index: VarId::Id,
    /// Variable name - may be `None` if the variable was introduced by Rust
    /// through desugaring.
    pub name: Option<String>,
    /// The variable type
    pub ty: Ty,
}

/// An expression body.
/// TODO: arg_count should be stored in GFunDecl below. But then,
///       the print is obfuscated and Aeneas may need some refactoring.
#[derive(Debug, Clone, Serialize)]
pub struct GExprBody<T> {
    pub meta: Meta,
    /// The number of local variables used for the input arguments.
    pub arg_count: usize,
    /// The local variables.
    /// We always have:
    /// - the local used for the return value
    /// - the input arguments
    /// - the remaining locals, used for the intermediate computations
    pub locals: VarId::Vector<Var>,
    pub body: T,
}

/// Function kind: "regular" function, trait method declaration, etc.
///
/// Example:
/// ========
/// ```text
/// trait Foo {
///   fn bar(x : u32) -> u32; // trait method: declaration
///
///   fn baz(x : bool) -> bool { x } // trait method: provided
/// }
///
/// impl Foo for ... {
///   fn bar(x : u32) -> u32 { x } // trait method: implementation
/// }
///
/// fn test(...) { ... } // regular
///
/// impl Type {
///   fn test(...) { ... } // regular
/// }
/// ```
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub enum FunKind {
    /// A "normal" function
    Regular,
    /// Trait method implementation
    TraitMethodImpl {
        /// The trait implementation block the method belongs to
        impl_id: TraitImplId::Id,
        /// The id of the trait decl the method belongs to
        trait_id: TraitDeclId::Id,
        /// The name of the method
        method_name: TraitItemName,
        /// True if this function re-implements a provided method
        provided: bool,
    },
    /// Trait method declaration
    TraitMethodDecl(TraitDeclId::Id, TraitItemName),
    /// Trait method provided function (trait method declaration which defines
    /// a default implementation at the same time)
    TraitMethodProvided(TraitDeclId::Id, TraitItemName),
}

/// A function definition
#[derive(Debug, Clone, Serialize)]
pub struct GFunDecl<T> {
    pub def_id: FunDeclId::Id,
    /// The meta data associated with the declaration.
    pub meta: Meta,
    /// [true] if the decl is a local decl, [false] if it comes from
    /// an external crate.
    pub is_local: bool,
    pub name: Name,
    /// The signature contains the inputs/output types *with* non-erased regions.
    /// It also contains the list of region and type parameters.
    pub signature: FunSig,
    /// The function kind: "regular" function, trait method declaration, etc.
    pub kind: FunKind,
    /// The function body, in case the function is not opaque.
    /// Opaque functions are: external functions, or local functions tagged
    /// as opaque.
    pub body: Option<GExprBody<T>>,
}

/// A global variable definition, either opaque or transparent.
#[derive(Debug, Clone, Serialize)]
pub struct GGlobalDecl<T> {
    pub def_id: GlobalDeclId::Id,
    /// The meta data associated with the declaration.
    pub meta: Meta,
    /// [true] if the decl is a local decl, [false] if it comes from
    /// an external crate.
    pub is_local: bool,
    pub name: Name,
    pub ty: Ty,
    pub body: Option<GExprBody<T>>,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TraitItemName(pub String);

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
/// The use case we have in mind is [std::iter::Iterator]: it declares one required
/// method (`next`) that should be implemented for every iterator, and defines many
/// helpers like `all`, `map`, etc. that shouldn't be re-implemented.
/// Of course, this forbids other useful use cases such as visitors implemented
/// by means of traits.
#[derive(Debug, Clone, Serialize)]
pub struct TraitDecl {
    pub def_id: TraitDeclId::Id,
    /// [true] if the decl is a local decl, [false] if it comes from
    /// an external crate.
    pub is_local: bool,
    pub name: Name,
    pub meta: Meta,
    pub generics: GenericParams,
    pub preds: Predicates,
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
    pub parent_clauses: TraitClauseId::Vector<TraitClause>,
    /// The associated constants declared in the trait.
    ///
    /// The optional id is for the default value.
    pub consts: Vec<(TraitItemName, (Ty, Option<GlobalDeclId::Id>))>,
    /// The associated types declared in the trait.
    pub types: Vec<(TraitItemName, (Vec<TraitClause>, Option<Ty>))>,
    /// The *required* methods.
    ///
    /// The required methods are the methods declared by the trait but with
    /// no default implementation.
    pub required_methods: Vec<(TraitItemName, FunDeclId::Id)>,
    /// The *provided* methods.
    ///
    /// The provided methods are the methods with a default implementation.
    ///
    /// We include the [FunDeclId::Id] identifiers *only* for the local
    /// trait declarations. Otherwise, it would mean we extract *all* the
    /// provided methods, which is not something we want to do *yet* for
    /// the external traits.
    ///
    /// TODO: allow to optionnaly extract information. For instance: attempt
    /// to extract, and fail nicely if we don't succeed (definition not in
    /// the supported subset, etc.).
    pub provided_methods: Vec<(TraitItemName, Option<FunDeclId::Id>)>,
}

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
#[derive(Debug, Clone, Serialize)]
pub struct TraitImpl {
    pub def_id: TraitImplId::Id,
    /// [true] if the decl is a local decl, [false] if it comes from
    /// an external crate.
    pub is_local: bool,
    pub name: Name,
    pub meta: Meta,
    /// The information about the implemented trait.
    /// Note that this contains the instantiation of the "parent"
    /// clauses.
    pub impl_trait: TraitDeclRef,
    pub generics: GenericParams,
    pub preds: Predicates,
    /// The trait references for the parent clauses (see [TraitDecl]).
    pub parent_trait_refs: TraitClauseId::Vector<TraitRef>,
    /// The associated constants declared in the trait.
    pub consts: Vec<(TraitItemName, (Ty, GlobalDeclId::Id))>,
    /// The associated types declared in the trait.
    pub types: Vec<(TraitItemName, (Vec<TraitRef>, Ty))>,
    /// The implemented required methods
    pub required_methods: Vec<(TraitItemName, FunDeclId::Id)>,
    /// The re-implemented provided methods
    pub provided_methods: Vec<(TraitItemName, FunDeclId::Id)>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Call {
    pub func: FnPtr,
    pub args: Vec<Operand>,
    pub dest: Place,
}
