//! Definitions common to [crate::ullbc_ast] and [crate::llbc_ast]
pub use crate::expressions::*;
pub use crate::gast_utils::*;
use crate::generate_index_type;
use crate::ids::Vector;
use crate::llbc_ast;
use crate::meta::{ItemMeta, Span};
use crate::names::Name;
pub use crate::types::GlobalDeclId;
pub use crate::types::TraitClauseId;
use crate::types::*;
pub use crate::types::{
    GenericArgs, GenericParams, TraitDeclId, TraitImplId, TraitInstanceId, TraitRef,
};
use crate::ullbc_ast;
use macros::EnumIsA;
use macros::EnumToGetters;
use serde::{Deserialize, Serialize};

generate_index_type!(FunDeclId, "Fun");
generate_index_type!(BodyId, "Body");

/// For use when deserializing.
fn dummy_def_id() -> rustc_hir::def_id::DefId {
    use rustc_hir::def_id::*;
    DefId {
        krate: CrateNum::MAX,
        index: DefIndex::MAX,
    }
}

/// A variable
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Var {
    /// Unique index identifying the variable
    pub index: VarId,
    /// Variable name - may be `None` if the variable was introduced by Rust
    /// through desugaring.
    pub name: Option<String>,
    /// The variable type
    pub ty: Ty,
}

/// Marker to indicate that a declaration is opaque (i.e. we don't inspect its body).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Opaque;

/// An expression body.
/// TODO: arg_count should be stored in GFunDecl below. But then,
///       the print is obfuscated and Aeneas may need some refactoring.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GExprBody<T> {
    pub span: Span,
    /// The number of local variables used for the input arguments.
    pub arg_count: usize,
    /// The local variables.
    /// We always have:
    /// - the local used for the return value
    /// - the input arguments
    /// - the remaining locals, used for the intermediate computations
    pub locals: Vector<VarId, Var>,
    pub body: T,
}

/// The body of a function or a constant.
#[derive(Debug, Clone, Serialize, Deserialize, EnumIsA, EnumToGetters)]
pub enum Body {
    /// Body represented as a CFG. This is what ullbc is made of, and what we get after translating MIR.
    Unstructured(ullbc_ast::ExprBody),
    /// Body represented with structured control flow. This is what llbc is made of. We restructure
    /// the control flow in `ullbc_to_llbc`.
    Structured(llbc_ast::ExprBody),
}

/// Item kind kind: "regular" item (not linked to a trait), trait item declaration, etc.
///
/// Example:
/// ========
/// ```text
/// trait Foo {
///   fn bar(x : u32) -> u32; // trait item: declaration (required)
///
///   fn baz(x : bool) -> bool { x } // trait item: provided
/// }
///
/// impl Foo for ... {
///   fn bar(x : u32) -> u32 { x } // trait item: implementation
/// }
///
/// fn test(...) { ... } // regular
///
/// impl Type {
///   fn test(...) { ... } // regular
/// }
/// ```
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ItemKind {
    /// A "normal" function
    Regular,
    /// Trait item implementation
    TraitItemImpl {
        /// The trait implementation block the method belongs to
        impl_id: TraitImplId,
        /// The id of the trait decl the method belongs to
        trait_id: TraitDeclId,
        /// The name of the item
        item_name: TraitItemName,
        /// True if this item *re-implements* a provided item
        provided: bool,
    },
    /// Trait item declaration
    TraitItemDecl(TraitDeclId, TraitItemName),
    /// Provided trait item (trait item declaration which defines
    /// a default implementation at the same time)
    TraitItemProvided(TraitDeclId, TraitItemName),
}

/// A function definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunDecl {
    pub def_id: FunDeclId,
    #[serde(skip)]
    #[serde(default = "dummy_def_id")]
    pub rust_id: rustc_hir::def_id::DefId,
    /// The meta data associated with the declaration.
    pub item_meta: ItemMeta,
    /// [true] if the decl is a local decl, [false] if it comes from
    /// an external crate.
    pub is_local: bool,
    pub name: Name,
    /// The signature contains the inputs/output types *with* non-erased regions.
    /// It also contains the list of region and type parameters.
    pub signature: FunSig,
    /// The function kind: "regular" function, trait method declaration, etc.
    pub kind: ItemKind,
    /// The function body, unless the function is opaque.
    /// Opaque functions are: external functions, or local functions tagged
    /// as opaque.
    pub body: Result<BodyId, Opaque>,
}

/// A global variable definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobalDecl {
    pub def_id: GlobalDeclId,
    #[serde(skip)]
    #[serde(default = "dummy_def_id")]
    pub rust_id: rustc_hir::def_id::DefId,
    /// The meta data associated with the declaration.
    pub item_meta: ItemMeta,
    /// [true] if the decl is a local decl, [false] if it comes from
    /// an external crate.
    pub is_local: bool,
    pub name: Name,
    pub generics: GenericParams,
    pub preds: Predicates,
    pub ty: Ty,
    /// The global kind: "regular" function, trait const declaration, etc.
    pub kind: ItemKind,
    pub body: Result<BodyId, Opaque>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
#[allow(clippy::type_complexity)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitDecl {
    pub def_id: TraitDeclId,
    /// [true] if the decl is a local decl, [false] if it comes from
    /// an external crate.
    pub is_local: bool,
    pub item_meta: ItemMeta,
    pub name: Name,
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
    pub parent_clauses: Vector<TraitClauseId, TraitClause>,
    /// The associated constants declared in the trait.
    ///
    /// The optional id is for the default value.
    pub consts: Vec<(TraitItemName, (Ty, Option<GlobalDeclId>))>,
    /// The associated types declared in the trait.
    pub types: Vec<(
        TraitItemName,
        (Vector<TraitClauseId, TraitClause>, Option<Ty>),
    )>,
    /// The *required* methods.
    ///
    /// The required methods are the methods declared by the trait but with
    /// no default implementation.
    pub required_methods: Vec<(TraitItemName, FunDeclId)>,
    /// The *provided* methods.
    ///
    /// The provided methods are the methods with a default implementation.
    ///
    /// We include the [FunDeclId] identifiers *only* for the local
    /// trait declarations. Otherwise, it would mean we extract *all* the
    /// provided methods, which is not something we want to do *yet* for
    /// the external traits.
    ///
    /// TODO: allow to optionnaly extract information. For instance: attempt
    /// to extract, and fail nicely if we don't succeed (definition not in
    /// the supported subset, etc.).
    pub provided_methods: Vec<(TraitItemName, Option<FunDeclId>)>,
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
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitImpl {
    pub def_id: TraitImplId,
    /// [true] if the decl is a local decl, [false] if it comes from
    /// an external crate.
    pub is_local: bool,
    pub name: Name,
    pub item_meta: ItemMeta,
    /// The information about the implemented trait.
    /// Note that this contains the instantiation of the "parent"
    /// clauses.
    pub impl_trait: TraitDeclRef,
    pub generics: GenericParams,
    pub preds: Predicates,
    /// The trait references for the parent clauses (see [TraitDecl]).
    pub parent_trait_refs: Vector<TraitClauseId, TraitRef>,
    /// The associated constants declared in the trait.
    pub consts: Vec<(TraitItemName, (Ty, GlobalDeclId))>,
    /// The associated types declared in the trait.
    pub types: Vec<(TraitItemName, (Vec<TraitRef>, Ty))>,
    /// The implemented required methods
    pub required_methods: Vec<(TraitItemName, FunDeclId)>,
    /// The re-implemented provided methods
    pub provided_methods: Vec<(TraitItemName, FunDeclId)>,
}

/// A function operand is used in function calls.
/// It either designates a top-level function, or a place in case
/// we are using function pointers stored in local variables.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FnOperand {
    /// Regular case: call to a top-level function, trait method, etc.
    Regular(FnPtr),
    /// Use of a function pointer stored in a local variable
    Move(Place),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Call {
    pub func: FnOperand,
    pub args: Vec<Operand>,
    pub dest: Place,
}
