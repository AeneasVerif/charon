//! Definitions common to [crate::ullbc_ast] and [crate::llbc_ast]
#![allow(dead_code)]

pub use crate::expressions::{Operand, Place};
pub use crate::gast_utils::*;
use crate::meta::Meta;
use crate::names::GlobalName;
use crate::names::{FunName, Name};
use crate::regions_hierarchy::RegionGroups;
pub use crate::types::GlobalDeclId;
pub use crate::types::TraitClauseId;
use crate::types::*;
pub use crate::types::{
    EGenericArgs, ETraitRef, GenericArgs, GenericParams, RGenericArgs, RTraitRef, TraitDeclId,
    TraitInstanceId, TraitRef,
};
use crate::values::*;
use macros::generate_index_type;
use macros::{EnumAsGetters, EnumIsA, VariantName};
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
    pub ty: ETy,
}

/// We use this to store information about the parameters in parent blocks.
/// This is necessary because in the definitions we store *all* the generics,
/// including those coming from the outer impl block.
///
/// For instance:
/// ```text
/// impl Foo<T> {
///         ^^^
///       outer block generics
///   fn bar<U>(...)  { ... }
///         ^^^
///       generics local to the function bar
/// }
/// ```
///
/// In `bar` we store the generics: `[T, U]`.
///
/// We however sometimes need to make a distinction between those two kinds
/// of generics, in particular when manipulating traits. For instance:
///
/// ```text
/// impl<T> Foo for Bar<T> {
///   fn baz<U>(...)  { ... }
/// }
///
/// fn test(...) {
///    x.baz(...); // Here, we refer to the call as:
///                // > Foo<T>::baz<U>(...)
///                // If baz hadn't been a method implementation of a trait,
///                // we would have refered to it as:
///                // > baz<T, U>(...)
///                // The reason is that with traits, we refer to the whole
///                // trait implementation (as if it were a structure), then
///                // pick a specific method inside (as if projecting a field
///                // from a structure).
/// }
/// ```
///
/// **Remark**: Rust only allows refering to the generics of the immediately
/// outer block. For this reason, when we need to store the information about
/// the generics of the outer block(s), we need to do it only for one level
/// (this definitely makes things simpler).
#[derive(Debug, Clone, Serialize)]
pub struct ParamsInfo {
    pub num_region_params: usize,
    pub num_type_params: usize,
    pub num_const_generic_params: usize,
    pub num_trait_clauses: usize,
}

/// A function signature.
/// Note that a signature uses unerased lifetimes, while function bodies (and
/// execution) use erased lifetimes.
/// We need the functions' signatures *with* the region parameters in order
/// to correctly abstract those functions (number and signature of the backward
/// functions) - we only use regions for this purpose.
#[derive(Debug, Clone, Serialize)]
pub struct FunSig {
    pub generics: GenericParams,
    /// Optional fields, for trait methods only (see the comments in [ParamsInfo]).
    pub parent_params_info: Option<ParamsInfo>,
    pub inputs: Vec<RTy>,
    pub output: RTy,
    /// The lifetime's hierarchy between the different regions.
    /// We initialize it to a dummy value, and compute it once the whole
    /// crate has been translated from MIR.
    ///
    /// TODO: move to Aeneas.
    pub regions_hierarchy: RegionGroups,
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
        /// The id of the trait decl/impl the method belongs to
        trait_id: TraitDeclId::Id,
        method_name: TraitMethodName,
        /// True if this function re-implements a provided method
        provided: bool,
    },
    /// Trait method declaration
    TraitMethodDecl(TraitDeclId::Id, TraitMethodName),
    /// Trait method provided function (method in a trait declaration with a
    /// default implementation)
    TraitMethodProvided(TraitDeclId::Id, TraitMethodName),
}

/// A function definition
#[derive(Debug, Clone, Serialize)]
pub struct GFunDecl<T> {
    pub def_id: FunDeclId::Id,
    /// The meta data associated with the declaration.
    pub meta: Meta,
    pub name: FunName,
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
    pub name: GlobalName,
    pub ty: ETy,
    pub body: Option<GExprBody<T>>,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct TraitMethodName(pub String);

/// A trait declaration or a trait implementation.
///
/// For instance:
/// ```text
/// // Trait declaration
/// trait Foo {
///   type Bar;
///
///   fn baz(...);
///
///   fn test() -> bool { true } // provided method (see below)
/// }
///
/// // Trait implementation
/// impl Foo for List {
///   type Bar = ...
///
///   fn baz(...) { ... }
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
#[derive(Debug, Clone, Serialize)]
pub struct TraitDecl {
    pub def_id: TraitDeclId::Id,
    /// If this is a trait implementation, contains the id of the trait
    /// declaration is implements.
    pub of_trait_id: Option<TraitDeclId::Id>,
    pub name: Name,
    pub generics: GenericParams,
    // The associated types declared in the trait
    //pub types:
    // The associated constants declared in the trait
    //
    /// The associated functions declared in the trait
    pub functions: Vec<(TraitMethodName, FunDeclId::Id)>,
}

/// A function identifier. See [crate::ullbc_ast::Terminator]
#[derive(Debug, Clone, EnumIsA, EnumAsGetters, VariantName, Serialize)]
pub enum FunId {
    /// A "regular" function (function local to the crate, external function
    /// not treated as a primitive one).
    Regular(FunDeclId::Id),
    /// A primitive function, coming from a standard library (for instance:
    /// `alloc::boxed::Box::new`).
    /// TODO: rename to "Primitive"
    Assumed(AssumedFunId),
}

/// An assumed function identifier, identifying a function coming from a
/// standard library.
#[derive(Debug, Clone, Copy, EnumIsA, EnumAsGetters, VariantName, Serialize)]
pub enum AssumedFunId {
    /// `core::mem::replace`
    Replace,
    /// `alloc::boxed::Box::new`
    BoxNew,
    /// `core::ops::deref::Deref::<alloc::boxed::Box<T>>::deref`
    BoxDeref,
    /// `core::ops::deref::DerefMut::<alloc::boxed::Box<T>>::deref_mut`
    BoxDerefMut,
    /// `alloc::alloc::box_free`
    /// This is actually an unsafe function, but the rust compiler sometimes
    /// introduces it when going to MIR.
    ///
    /// Also, in practice, deallocation is performed as follows in MIR:
    /// ```text
    /// alloc::alloc::box_free::<T, std::alloc::Global>(
    ///     move (b.0: std::ptr::Unique<T>),
    ///     move (b.1: std::alloc::Global))
    /// ```
    /// When translating from MIR to ULLBC, we do as if the MIR was actually the
    /// following (this is hardcoded - see [crate::register] and [crate::translate_functions_to_ullbc]):
    /// ```text
    /// alloc::alloc::box_free::<T>(move b)
    /// ```
    ///
    /// Also see the comments in [crate::assumed::type_to_used_params].
    BoxFree,
    /// `alloc::vec::Vec::new`
    VecNew,
    /// `alloc::vec::Vec::push`
    VecPush,
    /// `alloc::vec::Vec::insert`
    VecInsert,
    /// `alloc::vec::Vec::len`
    VecLen,
    /// `core::ops::index::Index::index<alloc::vec::Vec<T>, usize>`
    VecIndex,
    /// `core::ops::index::IndexMut::index_mut<alloc::vec::Vec<T>, usize>`
    VecIndexMut,
    /// Converted from [ProjectionElem::Index].
    ///
    /// Signature: `fn<T,N>(&[T;N], usize) -> &T`
    ArrayIndexShared,
    /// Converted from [ProjectionElem::Index].
    ///
    /// Signature: `fn<T,N>(&mut [T;N], usize) -> &mut T`
    ArrayIndexMut,
    /// Cast an array as a slice.
    ///
    /// Converted from [UnOp::ArrayToSlice]
    ArrayToSliceShared,
    /// Cast an array as a slice.
    ///
    /// Converted from [UnOp::ArrayToSlice]
    ArrayToSliceMut,
    /// Take a subslice from an array.
    ///
    /// Introduced by disambiguating the `Index::index` trait (takes a range
    /// as argument).
    ///
    /// TODO: there are a lot of shared/mut version. Parameterize them with
    /// a mutability attribute?
    ArraySubsliceShared,
    /// Take a subslice from an array.
    ///
    /// Introduced by disambiguating the `Index::index` trait (takes a range
    /// as argument).
    ArraySubsliceMut,
    /// Remark: when we write `a.len()` in Rust, where `a` is an array, the
    /// statement is desugared to a conversion from array to slice, followed
    /// by a call to the `len` function for slices.
    ///
    /// Signature: `fn<T>(&[T]) -> usize`
    SliceLen,
    /// Converted from [ProjectionElem::Index].
    ///
    /// Signature: `fn<T>(&[T], usize) -> &T`
    SliceIndexShared,
    /// Converted from [ProjectionElem::Index].
    ///
    /// Signature: `fn<T>(&mut [T], usize) -> &mut T`
    SliceIndexMut,
    /// Take a subslice from a slice.
    ///
    /// Introduced by disambiguating the `Index::index` trait (takes a range
    /// as argument).
    SliceSubsliceShared,
    /// Take a subslice from a slice.
    ///
    /// Introduced by disambiguating the `Index::index` trait (takes a range
    /// as argument).
    SliceSubsliceMut,
}

#[derive(Debug, Clone, Serialize)]
pub enum FunIdOrTraitMethodRef {
    Fun(FunId),
    /// If a trait: the reference to the trait and the id of the trait method
    Trait(ETraitRef, TraitMethodName),
}

#[derive(Debug, Clone, Serialize)]
pub struct Call {
    pub func: FunIdOrTraitMethodRef,
    pub generics: EGenericArgs,
    /// If this is a call to a trait method: stores *all* the generic arguments
    /// which apply to the trait + the method. The fields [region_args], [type_args]
    /// [const_generic_args] only store the arguments which concern the method call.
    /// See the comments for [ParamsInfo].
    pub trait_and_method_generic_args: Option<EGenericArgs>,
    pub args: Vec<Operand>,
    pub dest: Place,
}
