use crate::ast::*;
use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters, VariantIndexArity, VariantName};
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};

/// A type.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[serde_state(state_implements = DedupSerializerState)] // Avoid corecursive impls due to perfect derive
pub struct Ty(pub HashConsed<TyKind>);

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    VariantName,
    EnumIsA,
    EnumAsGetters,
    EnumToGetters,
    VariantIndexArity,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("T"))]
pub enum TyKind {
    /// An ADT.
    /// Note that here ADTs are very general. They can be:
    /// - user-defined ADTs
    /// - tuples (including `unit`, which is a 0-tuple)
    /// - built-in types, namely `Box` and `str`
    ///
    /// Note: this is incorrectly named: this can refer to any valid `TypeDecl` including extern
    /// types.
    Adt(TypeDeclRef),
    #[cfg_attr(feature = "charon_on_charon", charon::rename("TVar"))]
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
    TraitType(TraitRef, AssocTypeId, GenericArgs),
    /// `dyn Trait`
    DynTrait(DynPredicate),
    /// Function pointer type. This is a literal pointer to a region of memory that
    /// contains a callable function.
    /// This is a function signature with limited generics: it only supports lifetime generics, not
    /// other kinds of generics.
    FnPtr(RegionBinder<FunSig>),
    /// The unique type associated with each function item. Each function item is given
    /// a unique generic type that takes as input the function's early-bound generics. This type
    /// is not generally nameable in Rust; it's a ZST (there's a unique value), and a value of that type
    /// can be cast to a function pointer or passed to functions that expect `FnOnce`/`FnMut`/`Fn` parameters.
    /// There's a binder here because charon function items take both early and late-bound
    /// lifetimes as arguments; given that the type here is polymorpohic in the late-bound
    /// variables (those that could appear in a function pointer type like `for<'a> fn(&'a u32)`),
    /// we need to bind them here.
    FnDef(RegionBinder<FnPtr>),
    /// As a marker of taking out metadata from a given type
    /// The internal type is assumed to be a type variable
    PtrMetadata(Ty),
    /// An array type `[T; N]`
    Array(Ty, ConstantExpr),
    /// A slice type `[T]`
    Slice(Ty),
    /// A pattern type. This is a newtype over the first type whose valid values are restricted by
    /// the pattern.
    Pattern(Ty, TypePattern),
    /// A type that could not be computed or was incorrect.
    Error(String),
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
    DriveTwo,
    Hash,
    Ord,
    PartialOrd,
)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
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
    DriveTwo,
    Hash,
    Ord,
    PartialOrd,
)]
pub enum UIntTy {
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
    DriveTwo,
    Hash,
    Ord,
    PartialOrd,
)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("IntegerType"))]
pub enum IntegerTy {
    Signed(IntTy),
    Unsigned(UIntTy),
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
    DriveTwo,
    Hash,
    Ord,
    PartialOrd,
)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("FloatType"))]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
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
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
    Hash,
    Ord,
    PartialOrd,
)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("LiteralType"))]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("T"))]
#[serde_state(stateless)]
pub enum LiteralTy {
    Int(IntTy),
    UInt(UIntTy),
    Float(FloatTy),
    Bool,
    Char,
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
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
    Hash,
    Ord,
    PartialOrd,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("T"))]
pub enum BuiltinTy {
    /// A tuple `(A, B, ...)`, including `unit`.
    Tuple,
    /// Boxes; always detected, though they are only treated as primitives with `--treat-box-as-builtin`
    Box,
    /// The `str` type, which corresponds to a `[u8]` that encodes a string with UTF-8.
    Str,
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
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
    Ord,
    PartialOrd,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("R"))]
#[serde_state(stateless)]
pub enum RefKind {
    Mut,
    Shared,
}

/// The contents of a `dyn Trait` type.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct DynPredicate {
    /// This binder binds a single type `T`, which is considered existentially quantified. The
    /// predicates in the binder apply to `T` and represent the `dyn Trait` constraints.
    /// E.g. `dyn Iterator<Item=u32> + Send` is represented as `exists<T: Iterator<Item=u32> + Send> T`.
    ///
    /// Only the first trait clause may have methods. We use the vtable of this trait in the `dyn
    /// Trait` pointer metadata.
    pub binder: Binder<Ty>,
}

/// A type-level pattern used by [`TyKind::Pattern`].
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    VariantName,
    EnumIsA,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[serde_state(state_implements = DedupSerializerState)] // Avoid corecursive impls due to perfect derive
pub enum TypePattern {
    Range(ConstantExpr, ConstantExpr),
    OrPattern(Vec<TypePattern>),
    NotNull,
}

macro_rules! static_type {
    ($e:expr) => {{
        use std::sync::LazyLock;
        static TY: LazyLock<Ty> = LazyLock::new(|| $e.into_ty());
        TY.clone()
    }};
}

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

    /// Return the unit type
    pub fn mk_unit() -> Ty {
        static_type!(TyKind::Adt(TypeDeclRef {
            id: TypeDeclId::UNIT,
            generics: Box::new(GenericArgs::empty()),
            builtin: Some(BuiltinTy::Tuple),
        }))
    }

    pub fn mk_bool() -> Ty {
        static_type!(TyKind::Literal(LiteralTy::Bool))
    }

    pub fn mk_usize() -> Ty {
        static_type!(TyKind::Literal(LiteralTy::UInt(UIntTy::Usize)))
    }

    pub fn is_usize(&self) -> bool {
        matches!(self.kind(), TyKind::Literal(LiteralTy::UInt(UIntTy::Usize)))
    }

    pub fn mk_array(ty: Ty, len: ConstantExpr) -> Ty {
        TyKind::Array(ty, len).into_ty()
    }

    pub fn mk_slice(ty: Ty) -> Ty {
        TyKind::Slice(ty).into_ty()
    }
    /// Return true if it is actually unit (i.e.: 0-tuple)
    pub fn is_unit(&self) -> bool {
        *self == Ty::mk_unit()
    }

    /// Return true if this is a scalar type
    pub fn is_scalar(&self) -> bool {
        match self.kind() {
            TyKind::Literal(kind) => kind.is_int() || kind.is_uint(),
            TyKind::Pattern(ty, _) => ty.is_scalar(),
            _ => false,
        }
    }

    pub fn is_unsigned_scalar(&self) -> bool {
        match self.kind() {
            TyKind::Literal(LiteralTy::UInt(_)) => true,
            TyKind::Pattern(ty, _) => ty.is_unsigned_scalar(),
            _ => false,
        }
    }

    pub fn is_signed_scalar(&self) -> bool {
        match self.kind() {
            TyKind::Literal(LiteralTy::Int(_)) => true,
            TyKind::Pattern(ty, _) => ty.is_signed_scalar(),
            _ => false,
        }
    }

    pub fn is_str(&self) -> bool {
        match self.kind() {
            TyKind::Adt(ty_ref) => ty_ref.is_str(),
            _ => false,
        }
    }

    /// Return true if the type is Box
    pub fn is_box(&self) -> bool {
        match self.kind() {
            TyKind::Adt(ty_ref) => ty_ref.is_box(),
            _ => false,
        }
    }

    pub fn is_tuple(&self) -> bool {
        match self.kind() {
            TyKind::Adt(ty_ref) => ty_ref.is_tuple(),
            _ => false,
        }
    }

    pub fn as_adt_id(&self) -> Option<TypeDeclId> {
        self.kind().as_adt().map(|a| a.id)
    }

    pub fn get_ptr_metadata(&self, translated: &TranslatedCrate) -> PtrMetadata {
        let ty_decls = &translated.type_decls;
        match self.kind() {
            TyKind::Pattern(ty, _) => ty.get_ptr_metadata(translated),
            TyKind::Adt(ty_ref) => {
                // there are two cases:
                // 1. if the declared type has a fixed metadata, just returns it
                // 2. if it depends on some other types or the generic itself
                let Some(decl) = ty_decls.get(ty_ref.id) else {
                    return PtrMetadata::InheritFrom(self.clone());
                };
                match decl.ptr_metadata.clone().substitute(&ty_ref.generics) {
                    // if it depends on some type, recursion with the binding env
                    PtrMetadata::InheritFrom(ty) => ty.get_ptr_metadata(translated),
                    // otherwise, simply return it
                    meta => meta,
                }
            }
            TyKind::DynTrait(pred) => match pred.vtable_ref(translated) {
                Some(vtable) => PtrMetadata::VTable(vtable),
                None => PtrMetadata::InheritFrom(self.clone()),
            },
            // `[T]` has metadata length
            TyKind::Slice(..) => PtrMetadata::Length,
            TyKind::TraitType(..) | TyKind::TypeVar(_) => PtrMetadata::InheritFrom(self.clone()),
            TyKind::Literal(_)
            | TyKind::Never
            | TyKind::Ref(..)
            | TyKind::RawPtr(..)
            | TyKind::FnPtr(..)
            | TyKind::FnDef(..)
            | TyKind::Array(..)
            | TyKind::Error(_) => PtrMetadata::None,
            // The metadata itself must be Sized, hence must with `PtrMetadata::None`
            TyKind::PtrMetadata(_) => PtrMetadata::None,
        }
    }

    pub fn as_ref_or_ptr(&self) -> Option<&Ty> {
        match self.kind() {
            TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(ty),
            _ => None,
        }
    }

    pub fn as_array_or_slice(&self) -> Option<&Ty> {
        match self.kind() {
            TyKind::Slice(ty) | TyKind::Array(ty, _) => Some(ty),
            _ => None,
        }
    }

    /// The field types of a tuple, in order. Panics if the type is not a tuple,
    /// or if the type declaration is not found in the crate.
    pub fn as_tuple_fields(&self, translated: &TranslatedCrate) -> Vec<Ty> {
        let Some(tref) = self.as_adt().filter(|tref| tref.is_tuple()) else {
            unreachable!("as_tuple_fields called on non-tuple type {:?}", self);
        };

        // Avoid doing a substitution if the tuple is polymorphic and we can just
        // retrieve the fields from the generics, since substitutions won't work
        // in case `--unbind-item-vars` is set.
        let is_instantiated = translated
            .item_names
            .get(&ItemId::Type(tref.id))
            .map(|name| name.name.iter().any(|elem| elem.is_instantiated()))
            .unwrap_or(false);
        if !is_instantiated {
            return tref.generics.types.as_vec().clone();
        }

        translated
            .type_decls
            .get(tref.id)
            .and_then(|decl| decl.kind.as_struct())
            .expect("the declaration of specialized tuple {tref:?} is missing")
            .iter()
            .map(|f| f.ty.clone().substitute(&tref.generics))
            .collect()
    }

    pub fn as_adt(&self) -> Option<&TypeDeclRef> {
        self.kind().as_adt()
    }
}

impl TyKind {
    pub fn into_ty(self) -> Ty {
        Ty::new(self)
    }
}

impl IntegerTy {
    pub fn to_unsigned(&self) -> Self {
        match self {
            IntegerTy::Signed(IntTy::Isize) => IntegerTy::Unsigned(UIntTy::Usize),
            IntegerTy::Signed(IntTy::I8) => IntegerTy::Unsigned(UIntTy::U8),
            IntegerTy::Signed(IntTy::I16) => IntegerTy::Unsigned(UIntTy::U16),
            IntegerTy::Signed(IntTy::I32) => IntegerTy::Unsigned(UIntTy::U32),
            IntegerTy::Signed(IntTy::I64) => IntegerTy::Unsigned(UIntTy::U64),
            IntegerTy::Signed(IntTy::I128) => IntegerTy::Unsigned(UIntTy::U128),
            _ => *self,
        }
    }

    /// Important: this returns the target byte count for the types.
    /// Must not be used for host types from rustc.
    pub fn target_size(&self, ptr_size: ByteCount) -> usize {
        match self {
            IntegerTy::Signed(ty) => ty.target_size(ptr_size),
            IntegerTy::Unsigned(ty) => ty.target_size(ptr_size),
        }
    }
}

impl LiteralTy {
    pub fn to_integer_ty(&self) -> Option<IntegerTy> {
        match self {
            Self::Int(int_ty) => Some(IntegerTy::Signed(*int_ty)),
            Self::UInt(uint_ty) => Some(IntegerTy::Unsigned(*uint_ty)),
            _ => None,
        }
    }

    /// Important: this returns the target byte count for the types.
    /// Must not be used for host types from rustc.
    pub fn target_size(&self, ptr_size: ByteCount) -> usize {
        match self {
            LiteralTy::Int(int_ty) => int_ty.target_size(ptr_size),
            LiteralTy::UInt(uint_ty) => uint_ty.target_size(ptr_size),
            LiteralTy::Float(float_ty) => float_ty.target_size(),
            LiteralTy::Char => 4,
            LiteralTy::Bool => 1,
        }
    }
}

impl RefKind {
    pub fn mutable(x: bool) -> Self {
        if x { Self::Mut } else { Self::Shared }
    }
}

impl DynPredicate {
    /// Get a reference to the vtable type that corresponds to this predicate.
    pub fn vtable_ref(&self, translated: &TranslatedCrate) -> Option<TypeDeclRef> {
        let dyn_ty = TyKind::DynTrait(self.clone()).into_ty();
        // The first clause is the one relevant for the vtable. We're extracting it from our binder
        // so must give a value for the `Self` type.
        let relevant_tref = self.binder.params.trait_clauses[0]
            .trait_
            .clone()
            .erase()
            .substitute(&GenericArgs::new_types([dyn_ty].into()));

        // Get the vtable ref from the trait decl
        let trait_decl = translated.trait_decls.get(relevant_tref.id)?;
        let vtable_ref = trait_decl
            .vtable
            .clone()?
            .substitute_with_self(&relevant_tref.generics, &TraitRefKind::Dyn);
        Some(vtable_ref)
    }
}

impl From<LiteralTy> for Ty {
    fn from(value: LiteralTy) -> Self {
        TyKind::Literal(value).into_ty()
    }
}

impl From<TyKind> for Ty {
    fn from(kind: TyKind) -> Ty {
        kind.into_ty()
    }
}

/// Convenience impl.
impl std::ops::Deref for Ty {
    type Target = TyKind;

    fn deref(&self) -> &Self::Target {
        self.kind()
    }
}
