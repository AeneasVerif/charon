use crate::ids::Vector;
use crate::{ast::*, common::hash_consing::HashConsed};
use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters, VariantIndexArity, VariantName};
use serde::{Deserialize, Serialize};

mod vars;
pub use vars::*;

#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    Hash,
    PartialOrd,
    Ord,
    EnumIsA,
    EnumAsGetters,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
)]
#[charon::variants_prefix("R")]
pub enum Region {
    /// Region variable. See `DeBruijnVar` for details.
    Var(RegionDbVar),
    /// Static region
    Static,
    /// Erased region
    Erased,
}

/// Identifier of a trait instance.
/// This is derived from the trait resolution.
///
/// Should be read as a path inside the trait clauses which apply to the current
/// definition. Note that every path designated by `TraitInstanceId` refers
/// to a *trait instance*, which is why the [`TraitRefKind::Clause`] variant may seem redundant
/// with some of the other variants.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, Drive, DriveMut)]
#[charon::rename("TraitInstanceId")]
pub enum TraitRefKind {
    /// A specific top-level implementation item.
    TraitImpl(TraitImplId, BoxedArgs),

    /// One of the local clauses.
    ///
    /// Example:
    /// ```text
    /// fn f<T>(...) where T : Foo
    ///                    ^^^^^^^
    ///                    Clause(0)
    /// ```
    Clause(ClauseDbVar),

    /// A parent clause
    ///
    /// Remark: the [TraitDeclId] gives the trait declaration which is
    /// implemented by the instance id from which we take the parent clause
    /// (see example below). It is not necessary and included for convenience.
    ///
    /// Remark: Ideally we should store a full `TraitRef` instead, but hax does not give us enough
    /// information to get the right generic args.
    ///
    /// Example:
    /// ```text
    /// trait Foo1 {}
    /// trait Foo2 { fn f(); }
    ///
    /// trait Bar : Foo1 + Foo2 {}
    ///             ^^^^   ^^^^
    ///                    parent clause 1
    ///     parent clause 0
    ///
    /// fn g<T : Bar>(x : T) {
    ///   x.f()
    ///   ^^^^^
    ///   Parent(Clause(0), Bar, 1)::f(x)
    ///                          ^
    ///                          parent clause 1 of clause 0
    ///                     ^^^
    ///              clause 0 implements Bar
    /// }
    /// ```
    ParentClause(Box<TraitRefKind>, TraitDeclId, TraitClauseId),

    /// A clause defined on an associated type. This variant is only used during translation; after
    /// the `lift_associated_item_clauses` pass, clauses on items become `ParentClause`s.
    ///
    /// Remark: the [TraitDeclId] gives the trait declaration which is
    /// implemented by the trait implementation from which we take the item
    /// (see below). It is not necessary and provided for convenience.
    ///
    /// Example:
    /// ```text
    /// trait Foo {
    ///   type W: Bar0 + Bar1 // Bar1 contains a method bar1
    ///                  ^^^^
    ///               this is the clause 1 applying to W
    /// }
    ///
    /// fn f<T : Foo>(x : T::W) {
    ///   x.bar1();
    ///   ^^^^^^^
    ///   ItemClause(Clause(0), Foo, W, 1)
    ///                              ^^^^
    ///                              clause 1 from item W (from local clause 0)
    ///                         ^^^
    ///                local clause 0 implements Foo
    /// }
    /// ```
    #[charon::opaque]
    ItemClause(Box<TraitRefKind>, TraitDeclId, TraitItemName, TraitClauseId),

    /// The implicit `Self: Trait` clause. Present inside trait declarations, including trait
    /// method declarations. Not present in trait implementations as we can use `TraitImpl` intead.
    #[charon::rename("Self")]
    SelfId,

    /// A trait implementation that is computed by the compiler, such as for built-in traits
    /// `Sized` or `FnMut`. This morally points to an invisible `impl` block; as such it contains
    /// the information we may need from one.
    BuiltinOrAuto {
        trait_decl_ref: PolyTraitDeclRef,
        /// The `ImplExpr`s required to satisfy the implied predicates on the trait declaration.
        /// E.g. since `FnMut: FnOnce`, a built-in `T: FnMut` impl would have an `ImplExpr` for `T:
        /// FnOnce`.
        parent_trait_refs: Vector<TraitClauseId, TraitRef>,
        /// The values of the associated types for this trait.
        types: Vec<(TraitItemName, Ty)>,
    },

    /// The automatically-generated implementation for `dyn Trait`.
    Dyn(PolyTraitDeclRef),

    /// For error reporting.
    #[charon::rename("UnknownTrait")]
    #[drive(skip)]
    Unknown(String),
}

/// A reference to a trait
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, Drive, DriveMut)]
pub struct TraitRef {
    #[charon::rename("trait_id")]
    pub kind: TraitRefKind,
    /// Not necessary, but useful
    pub trait_decl_ref: PolyTraitDeclRef,
}

/// A predicate of the form `Type: Trait<Args>`.
///
/// About the generics, if we write:
/// ```text
/// impl Foo<bool> for String { ... }
/// ```
///
/// The substitution is: `[String, bool]`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, Drive, DriveMut)]
pub struct TraitDeclRef {
    #[charon::rename("trait_decl_id")]
    pub trait_id: TraitDeclId,
    #[charon::rename("decl_generics")]
    pub generics: BoxedArgs,
}

/// A quantified trait predicate, e.g. `for<'a> Type<'a>: Trait<'a, Args>`.
pub type PolyTraitDeclRef = RegionBinder<TraitDeclRef>;

/// A reference to a tait impl, using the provided arguments.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, Drive, DriveMut)]
pub struct TraitImplRef {
    #[charon::rename("trait_impl_id")]
    pub impl_id: TraitImplId,
    #[charon::rename("impl_generics")]
    pub generics: BoxedArgs,
}

/// .0 outlives .1
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Drive, DriveMut)]
pub struct OutlivesPred<T, U>(pub T, pub U);

pub type RegionOutlives = OutlivesPred<Region, Region>;
pub type TypeOutlives = OutlivesPred<Ty, Region>;

/// A constraint over a trait associated type.
///
/// Example:
/// ```text
/// T : Foo<S = String>
///         ^^^^^^^^^^
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Drive, DriveMut)]
pub struct TraitTypeConstraint {
    pub trait_ref: TraitRef,
    pub type_name: TraitItemName,
    pub ty: Ty,
}

/// Each `GenericArgs` is meant for a corresponding `GenericParams`; this describes which one.
#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize, Drive, DriveMut)]
#[charon::variants_prefix("GS")]
pub enum GenericsSource {
    /// A top-level item.
    Item(AnyTransId),
    /// A trait method.
    Method(TraitDeclId, TraitItemName),
    /// A builtin item like `Box`.
    Builtin,
    /// Some other use of generics outside the main Charon ast.
    #[charon::opaque]
    Other,
}

/// A set of generic arguments.
#[derive(Clone, Eq, PartialEq, Hash, Serialize, Deserialize, Drive, DriveMut)]
pub struct GenericArgs {
    pub regions: Vector<RegionId, Region>,
    pub types: Vector<TypeVarId, Ty>,
    pub const_generics: Vector<ConstGenericVarId, ConstGeneric>,
    // TODO: rename to match [GenericParams]?
    pub trait_refs: Vector<TraitClauseId, TraitRef>,
    #[charon::opaque]
    #[drive(skip)]
    /// Each `GenericArgs` is meant for a corresponding `GenericParams`; this records which one.
    pub target: GenericsSource,
}

pub type BoxedArgs = Box<GenericArgs>;

/// A value of type `T` bound by regions. We should use `binder` instead but this causes name clash
/// issues in the derived ocaml visitors.
/// TODO: merge with `binder`
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Drive, DriveMut)]
pub struct RegionBinder<T> {
    #[charon::rename("binder_regions")]
    pub regions: Vector<RegionId, RegionVar>,
    /// Named this way to highlight accesses to the inner value that might be handling parameters
    /// incorrectly. Prefer using helper methods.
    #[charon::rename("binder_value")]
    pub skip_binder: T,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Drive, DriveMut)]
#[charon::variants_prefix("BK")]
pub enum BinderKind {
    /// The parameters of a trait method. Used in the `methods` lists in trait decls and trait
    /// impls.
    TraitMethod(TraitDeclId, TraitItemName),
    /// The parameters bound in a non-trait `impl` block. Used in the `Name`s of inherent methods.
    InherentImplBlock,
    /// Some other use of a binder outside the main Charon ast.
    Other,
}

/// A value of type `T` bound by generic parameters. Used in any context where we're adding generic
/// parameters that aren't on the top-level item, e.g. `for<'a>` clauses (uses `RegionBinder` for
/// now), trait methods, GATs (TODO).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Drive, DriveMut)]
pub struct Binder<T> {
    #[charon::rename("binder_params")]
    pub params: GenericParams,
    /// Named this way to highlight accesses to the inner value that might be handling parameters
    /// incorrectly. Prefer using helper methods.
    #[charon::rename("binder_value")]
    pub skip_binder: T,
    /// The kind of binder this is.
    #[charon::opaque]
    #[drive(skip)]
    pub kind: BinderKind,
}

/// Generic parameters for a declaration.
/// We group the generics which come from the Rust compiler substitutions
/// (the regions, types and const generics) as well as the trait clauses.
/// The reason is that we consider that those are parameters that need to
/// be filled. We group in a different place the predicates which are not
/// trait clauses, because those enforce constraints but do not need to
/// be filled with witnesses/instances.
#[derive(Default, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Drive, DriveMut)]
pub struct GenericParams {
    pub regions: Vector<RegionId, RegionVar>,
    pub types: Vector<TypeVarId, TypeVar>,
    pub const_generics: Vector<ConstGenericVarId, ConstGenericVar>,
    // TODO: rename to match [GenericArgs]?
    pub trait_clauses: Vector<TraitClauseId, TraitClause>,
    /// The first region in the pair outlives the second region
    pub regions_outlive: Vec<RegionBinder<RegionOutlives>>,
    /// The type outlives the region
    pub types_outlive: Vec<RegionBinder<TypeOutlives>>,
    /// Constraints over trait associated types
    pub trait_type_constraints: Vector<TraitTypeConstraintId, RegionBinder<TraitTypeConstraint>>,
}

/// A predicate of the form `exists<T> where T: Trait`.
///
/// TODO: store something useful here
#[derive(Debug, Default, Clone, Hash, PartialEq, Eq, Serialize, Deserialize, Drive, DriveMut)]
pub struct ExistentialPredicate;

/// Where a given predicate came from.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Drive, DriveMut)]
pub enum PredicateOrigin {
    // Note: we use this for globals too, but that's only available with an unstable feature.
    // ```
    // fn function<T: Clone>() {}
    // fn function<T>() where T: Clone {}
    // const NONE<T: Copy>: Option<T> = None;
    // ```
    WhereClauseOnFn,
    // ```
    // struct Struct<T: Clone> {}
    // struct Struct<T> where T: Clone {}
    // type TypeAlias<T: Clone> = ...;
    // ```
    WhereClauseOnType,
    // Note: this is both trait impls and inherent impl blocks.
    // ```
    // impl<T: Clone> Type<T> {}
    // impl<T> Type<T> where T: Clone {}
    // impl<T> Trait for Type<T> where T: Clone {}
    // ```
    WhereClauseOnImpl,
    // The special `Self: Trait` clause which is in scope inside the definition of `Foo` or an
    // implementation of it.
    // ```
    // trait Trait {}
    // ```
    TraitSelf,
    // Note: this also includes supertrait constraints.
    // ```
    // trait Trait<T: Clone> {}
    // trait Trait<T> where T: Clone {}
    // trait Trait: Clone {}
    // ```
    WhereClauseOnTrait,
    // ```
    // trait Trait {
    //     type AssocType: Clone;
    // }
    // ```
    TraitItem(TraitItemName),
}

/// A type declaration.
///
/// Types can be opaque or transparent.
///
/// Transparent types are local types not marked as opaque.
/// Opaque types are the others: local types marked as opaque, and non-local
/// types (coming from external dependencies).
///
/// In case the type is transparent, the declaration also contains the
/// type definition (see [TypeDeclKind]).
///
/// A type can only be an ADT (structure or enumeration), as type aliases are
/// inlined in MIR.
#[derive(Debug, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct TypeDecl {
    #[drive(skip)]
    pub def_id: TypeDeclId,
    /// Meta information associated with the item.
    pub item_meta: ItemMeta,
    pub generics: GenericParams,
    /// The type kind: enum, struct, or opaque.
    pub kind: TypeDeclKind,
}

generate_index_type!(VariantId, "Variant");
generate_index_type!(FieldId, "Field");

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, Serialize, Deserialize, Drive, DriveMut)]
pub enum TypeDeclKind {
    Struct(Vector<FieldId, Field>),
    Enum(Vector<VariantId, Variant>),
    Union(Vector<FieldId, Field>),
    /// An opaque type.
    ///
    /// Either a local type marked as opaque, or an external type.
    Opaque,
    /// An alias to another type. This only shows up in the top-level list of items, as rustc
    /// inlines uses of type aliases everywhere else.
    Alias(Ty),
    /// Used if an error happened during the extraction, and we don't panic
    /// on error.
    #[charon::rename("TDeclError")]
    #[drive(skip)]
    Error(String),
}

#[derive(Debug, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct Variant {
    pub span: Span,
    #[drive(skip)]
    pub attr_info: AttrInfo,
    #[charon::rename("variant_name")]
    #[drive(skip)]
    pub name: String,
    pub fields: Vector<FieldId, Field>,
    /// The discriminant value outputted by `std::mem::discriminant` for this variant. This is
    /// different than the discriminant stored in memory (the one controlled by `repr`).
    pub discriminant: ScalarValue,
}

#[derive(Debug, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct Field {
    pub span: Span,
    #[drive(skip)]
    pub attr_info: AttrInfo,
    #[charon::rename("field_name")]
    #[drive(skip)]
    pub name: Option<String>,
    #[charon::rename("field_ty")]
    pub ty: Ty,
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    EnumIsA,
    VariantName,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
#[charon::rename("IntegerType")]
pub enum IntegerTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    EnumIsA,
    VariantName,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
#[charon::rename("FloatType")]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Copy,
    Hash,
    VariantName,
    EnumIsA,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Ord,
    PartialOrd,
)]
#[charon::variants_prefix("R")]
pub enum RefKind {
    Mut,
    Shared,
}

/// Type identifier.
///
/// Allows us to factorize the code for built-in types, adts and tuples
#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Copy,
    VariantName,
    EnumAsGetters,
    EnumIsA,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
#[charon::variants_prefix("T")]
pub enum TypeId {
    /// A "regular" ADT type.
    ///
    /// Includes transparent ADTs and opaque ADTs (local ADTs marked as opaque,
    /// and external ADTs).
    #[charon::rename("TAdtId")]
    Adt(TypeDeclId),
    Tuple,
    /// Built-in type. Either a primitive type like array or slice, or a
    /// non-primitive type coming from a standard library
    /// and that we handle like a primitive type. Types falling into this
    /// category include: Box, Vec, Cell...
    /// The Array and Slice types were initially modelled as primitive in
    /// the [Ty] type. We decided to move them to built-in types as it allows
    /// for more uniform treatment throughout the codebase.
    #[charon::rename("TBuiltin")]
    Builtin(BuiltinTy),
}

/// Types of primitive values. Either an integer, bool, char
#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Copy,
    VariantName,
    EnumIsA,
    EnumAsGetters,
    VariantIndexArity,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
#[charon::rename("LiteralType")]
#[charon::variants_prefix("T")]
pub enum LiteralTy {
    Integer(IntegerTy),
    Float(FloatTy),
    Bool,
    Char,
}

/// Const Generic Values. Either a primitive value, or a variable corresponding to a primitve value
#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    VariantName,
    EnumIsA,
    EnumAsGetters,
    VariantIndexArity,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Hash,
)]
#[charon::variants_prefix("Cg")]
pub enum ConstGeneric {
    /// A global constant
    Global(GlobalDeclId),
    /// A const generic variable
    Var(ConstGenericDbVar),
    /// A concrete value
    Value(Literal),
}

/// A type.
///
/// Warning: the `DriveMut` impls of `Ty` needs to clone and re-hash the modified type to maintain
/// the hash-consing invariant. This is expensive, avoid visiting types mutably when not needed.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub struct Ty(HashConsed<TyKind>);

impl Ty {
    pub fn new(kind: TyKind) -> Self {
        Ty(HashConsed::new(kind))
    }

    pub fn kind(&self) -> &TyKind {
        self.0.inner()
    }

    pub fn with_kind_mut<R>(&mut self, f: impl FnOnce(&mut TyKind) -> R) -> R {
        self.0.with_inner_mut(f)
    }
}

impl<'s, V: Visit<'s, TyKind>> Drive<'s, V> for Ty {
    fn drive_inner(&'s self, v: &mut V) -> std::ops::ControlFlow<V::Break> {
        self.0.drive_inner(v)
    }
}
/// This explores the type mutably by cloning and re-hashing afterwards.
impl<'s, V> DriveMut<'s, V> for Ty
where
    for<'a> V: VisitMut<'a, TyKind>,
{
    fn drive_inner_mut(&'s mut self, v: &mut V) -> std::ops::ControlFlow<V::Break> {
        self.0.drive_inner_mut(v)
    }
}

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    Hash,
    VariantName,
    EnumIsA,
    EnumAsGetters,
    EnumToGetters,
    VariantIndexArity,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
)]
#[charon::variants_prefix("T")]
#[charon::rename("Ty")]
pub enum TyKind {
    /// An ADT.
    /// Note that here ADTs are very general. They can be:
    /// - user-defined ADTs
    /// - tuples (including `unit`, which is a 0-tuple)
    /// - built-in types (includes some primitive types, e.g., arrays or slices)
    /// The information on the nature of the ADT is stored in (`TypeId`)[TypeId].
    /// The last list is used encode const generics, e.g., the size of an array
    ///
    /// Note: this is incorrectly named: this can refer to any valid `TypeDecl` including extern
    /// types.
    Adt(TypeId, GenericArgs),
    /// A closure type, which is essentially a struct with builtin impls. Currently we don't
    /// translate the struct itself, only the function item that contains the closure's code.
    Closure {
        /// The FunDecl item containing the code of the closure. That function takes the closure
        /// state as its first argument.
        fun_id: FunDeclId,
        /// Generics that apply to the parent of this closure.
        /// Warning: hax may not handle nexted closure correctly yet.
        parent_args: BoxedArgs,
        /// The types of the variables captured by this closure.
        upvar_tys: Vec<Ty>,
        /// The signature of the function that this closure represents.
        signature: RegionBinder<(Vec<Ty>, Ty)>,
    },
    #[charon::rename("TVar")]
    TypeVar(TypeDbVar),
    Literal(LiteralTy),
    /// The never type, for computations which don't return. It is sometimes
    /// necessary for intermediate variables. For instance, if we do (coming
    /// from the rust documentation):
    /// ```text
    /// let num: u32 = match get_a_number() {
    ///     Some(num) => num,
    ///     None => break,
    /// };
    /// ```
    /// the second branch will have type `Never`. Also note that `Never`
    /// can be coerced to any type.
    ///
    /// Note that we eliminate the variables which have this type in a micro-pass.
    /// As statements don't have types, this type disappears eventually disappears
    /// from the AST.
    Never,
    // We don't support floating point numbers on purpose (for now)
    /// A borrow
    Ref(Region, Ty, RefKind),
    /// A raw pointer.
    RawPtr(Ty, RefKind),
    /// A trait associated type
    ///
    /// Ex.:
    /// ```text
    /// trait Foo {
    ///   type Bar; // type associated to the trait Foo
    /// }
    /// ```
    TraitType(TraitRef, TraitItemName),
    /// `dyn Trait`
    ///
    /// This carries an existentially quantified list of predicates, e.g. `exists<T> where T:
    /// Into<u64>`. The predicate must quantify over a single type and no any regions or constants.
    ///
    /// TODO: we don't translate this properly yet.
    DynTrait(ExistentialPredicate),
    /// Arrow type, used for function pointers and reused for the unique type associated with each
    /// function item.
    /// This is a function signature with limited generics: it only supports lifetime generics, not
    /// other kinds of
    /// generics.
    Arrow(RegionBinder<(Vec<Ty>, Ty)>),
    /// A type that could not be computed or was incorrect.
    #[drive(skip)]
    Error(String),
}

/// Builtin types identifiers.
///
/// WARNING: for now, all the built-in types are covariant in the generic
/// parameters (if there are). Adding types which don't satisfy this
/// will require to update the code abstracting the signatures (to properly
/// take into account the lifetime constraints).
///
/// TODO: update to not hardcode the types (except `Box` maybe) and be more
/// modular.
/// TODO: move to builtins.rs?
#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    Copy,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    Hash,
    Ord,
    PartialOrd,
)]
#[charon::variants_prefix("T")]
pub enum BuiltinTy {
    /// Boxes are de facto a primitive type.
    Box,
    /// Primitive type
    Array,
    /// Primitive type
    Slice,
    /// Primitive type
    Str,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Serialize, Deserialize, Drive, DriveMut)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

/// Additional information for closures.
/// We mostly use it in micro-passes like [crate::transform::update_closure_signatures].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Drive, DriveMut)]
pub struct ClosureInfo {
    pub kind: ClosureKind,
    /// Contains the types of the fields in the closure state.
    /// More precisely, for every place captured by the
    /// closure, the state has one field (typically a ref).
    ///
    /// For instance, below the closure has a state with two fields of type `&u32`:
    /// ```text
    /// pub fn test_closure_capture(x: u32, y: u32) -> u32 {
    ///   let f = &|z| x + y + z;
    ///   (f)(0)
    /// }
    /// ```
    pub state: Vector<TypeVarId, Ty>,
}

/// A function signature.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Drive, DriveMut)]
pub struct FunSig {
    /// Is the function unsafe or not
    #[drive(skip)]
    pub is_unsafe: bool,
    /// `true` if the signature is for a closure.
    ///
    /// Importantly: if the signature is for a closure, then:
    /// - the type and const generic params actually come from the parent function
    ///   (the function in which the closure is defined)
    /// - the region variables are local to the closure
    #[drive(skip)]
    pub is_closure: bool,
    /// Additional information if this is the signature of a closure.
    pub closure_info: Option<ClosureInfo>,
    pub generics: GenericParams,
    pub inputs: Vec<Ty>,
    pub output: Ty,
}
