use std::cmp::{Ord, PartialOrd};

use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};

use crate::ast::*;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};

generate_index_type!(FunDeclId, "Fun");
generate_index_type!(TypeDeclId, "Adt");

impl TypeDeclId {
    /// The declaration of the unit type `()`. With `--no-gen-tuple-structs`, this is the
    /// declaration of every tuple.
    pub const UNIT: Self = Self::ZERO;
}
generate_index_type!(GlobalDeclId, "Global");
generate_index_type!(TraitDeclId, "TraitDecl");
generate_index_type!(TraitImplId, "TraitImpl");

/// The id of a translated item.
#[derive(
    Copy,
    Clone,
    Debug,
    PartialOrd,
    Ord,
    PartialEq,
    Eq,
    Hash,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    VariantIndexArity,
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Id"))]
#[serde_state(stateless)]
pub enum ItemId {
    Type(TypeDeclId),
    TraitDecl(TraitDeclId),
    TraitImpl(TraitImplId),
    Fun(FunDeclId),
    Global(GlobalDeclId),
}

/// The id of an associated item within a trait.
#[derive(
    Copy,
    Clone,
    Debug,
    PartialOrd,
    Ord,
    PartialEq,
    Eq,
    Hash,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    VariantIndexArity,
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("AssocId"))]
#[serde_state(stateless)]
pub enum AssocItemId {
    Type(AssocTypeId),
    Method(TraitMethodId),
    Const(AssocConstId),
}

/// The id of a translated item or associated item definition.
#[derive(
    Copy,
    Clone,
    Debug,
    PartialOrd,
    Ord,
    PartialEq,
    Eq,
    Hash,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    VariantIndexArity,
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Item"))]
#[serde_state(stateless)]
pub enum MaybeAssocItemId {
    Free(ItemId),
    Assoc(TraitDeclId, AssocItemId),
}

/// Reference to a type declaration.
///
/// This includes user-defined ADTs (structs, enums, unions), but also tuples,
/// boxes, and `str`, which we translate as `struct str([u8])`.
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
pub struct TypeDeclRef {
    pub id: TypeDeclId,
    pub generics: BoxedArgs,
    /// If this points to a built-in type, it is recorded here for easier identification.
    pub builtin: Option<BuiltinTy>,
}

/// Reference to a function declaration.
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
pub struct FunDeclRef {
    pub id: FunDeclId,
    /// Generic arguments passed to the function.
    pub generics: BoxedArgs,
}

/// A regular function.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("F"))]
#[serde_state(stateless)]
pub enum FunId {
    /// A "regular" function (function local to the crate, external function
    /// not treated as a primitive one).
    Regular(FunDeclId),
}

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    EnumAsGetters,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
    Hash,
)]
pub enum FnPtrKind {
    #[cfg_attr(feature = "charon_on_charon", charon::rename("FunId"))]
    Fun(FunId),
    /// If a trait: the reference to the trait and the id of the trait method.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("TraitMethod"))]
    Trait(TraitRef, TraitMethodId),
}

/// Reference to a function, possibly indirected via a trait.
#[derive(
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Clone,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct FnPtr {
    pub kind: Box<FnPtrKind>,
    pub generics: BoxedArgs,
}

/// Reference to a global declaration.
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
pub struct GlobalDeclRef {
    pub id: GlobalDeclId,
    pub generics: BoxedArgs,
}

/// A predicate of the form `Type: Trait<Args>`.
///
/// About the generics, if we write:
/// ```text
/// impl Foo<bool> for String { ... }
/// ```
///
/// The substitution is: `[String, bool]`.
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
pub struct TraitDeclRef {
    pub id: TraitDeclId,
    pub generics: BoxedArgs,
}

/// A reference to a tait impl, using the provided arguments.
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
pub struct TraitImplRef {
    pub id: TraitImplId,
    pub generics: BoxedArgs,
}

impl TypeDeclRef {
    pub fn new(id: TypeDeclId, generics: GenericArgs, builtin: Option<BuiltinTy>) -> Self {
        Self {
            id,
            generics: Box::new(generics),
            builtin,
        }
    }

    pub fn as_builtin(&self) -> Option<BuiltinTy> {
        self.builtin
    }

    /// Whether this refers to `Box`.
    pub fn is_box(&self) -> bool {
        matches!(self.builtin, Some(BuiltinTy::Box))
    }

    /// Whether this refers to a tuple.
    pub fn is_tuple(&self) -> bool {
        matches!(self.builtin, Some(BuiltinTy::Tuple))
    }

    /// Whether this refers to `str`.
    pub fn is_str(&self) -> bool {
        matches!(self.builtin, Some(BuiltinTy::Str))
    }
}

impl TraitDeclRef {
    pub fn self_ty<'a>(&'a self, krate: &'a TranslatedCrate) -> Option<&'a Ty> {
        match self.generics.types.iter().next() {
            Some(ty) => Some(ty),
            // TODO(mono): A monomorphized trait takes no arguments.
            None => {
                let name = krate.item_name(self.id);
                let args = name.name.last()?.as_monomorphized()?;
                args.types.iter().next()
            }
        }
    }
}

impl FnPtr {
    pub fn new(kind: FnPtrKind, generics: impl Into<BoxedArgs>) -> Self {
        Self {
            kind: Box::new(kind),
            generics: generics.into(),
        }
    }

    /// Get the generics for the pre-monomorphization item.
    pub fn pre_mono_generics<'a>(&'a self, krate: &'a TranslatedCrate) -> &'a GenericArgs {
        match *self.kind {
            FnPtrKind::Fun(FunId::Regular(fun_id)) => krate
                .item_name(fun_id)
                .mono_args()
                .unwrap_or(&self.generics),
            // Can't happen in mono mode.
            FnPtrKind::Trait(..) => &self.generics,
        }
    }
}

/// A generic `*DeclRef`-shaped struct, used when we're generic over the type of item.
#[derive(Debug, PartialEq, Eq, Clone, Drive, DriveMut, DriveTwo)]
pub struct DeclRef<Id> {
    pub id: Id,
    pub generics: BoxedArgs,
    /// If the item is a trait associated item, `generics` are only those of the item, and this
    /// contains a reference to the trait.
    // TODO: also store `AssocItemId` so that we can convert to `FnPtr` without
    // `MaybeBuiltinFunDeclRef`.
    pub trait_ref: Option<TraitRef>,
}

impl DeclRef<ItemId> {
    pub fn try_convert_id<Id>(self) -> Result<DeclRef<Id>, <ItemId as TryInto<Id>>::Error>
    where
        ItemId: TryInto<Id>,
    {
        Ok(DeclRef {
            id: self.id.try_into()?,
            generics: self.generics,
            trait_ref: self.trait_ref,
        })
    }
}

// Implement `DeclRef<_>` -> `FooDeclRef` conversions.
macro_rules! convert_item_ref {
    ($item_ref_ty:ident($id:ident)) => {
        impl TryFrom<DeclRef<ItemId>> for $item_ref_ty {
            type Error = ();
            fn try_from(item: DeclRef<ItemId>) -> Result<Self, ()> {
                assert!(item.trait_ref.is_none());
                Ok($item_ref_ty {
                    id: item.id.try_into()?,
                    generics: item.generics,
                })
            }
        }
        impl From<DeclRef<$id>> for $item_ref_ty {
            fn from(item: DeclRef<$id>) -> Self {
                assert!(item.trait_ref.is_none());
                $item_ref_ty {
                    id: item.id,
                    generics: item.generics,
                }
            }
        }
    };
}
// We do not provide a `DeclRef<_> -> TypeDeclRef` impl, because we lack information
// about builtins here.
convert_item_ref!(FunDeclRef(FunDeclId));
convert_item_ref!(GlobalDeclRef(GlobalDeclId));
convert_item_ref!(TraitDeclRef(TraitDeclId));
convert_item_ref!(TraitImplRef(TraitImplId));
impl TryFrom<DeclRef<ItemId>> for FnPtr {
    type Error = ();
    fn try_from(item: DeclRef<ItemId>) -> Result<Self, ()> {
        if item.trait_ref.is_some() {
            panic!(
                "converting `DeclRef<ItemId>` to `FnPtr` cannot
                deal with the trait method case."
            )
        }
        let id: FunId = item.id.try_into()?;
        Ok(FnPtr::new(id.into(), item.generics))
    }
}
impl From<FunDeclRef> for FnPtr {
    fn from(fn_ref: FunDeclRef) -> Self {
        FnPtr::new(fn_ref.id.into(), fn_ref.generics)
    }
}

/// Implement `TryFrom`  and `From` to convert between an enum and its variants.
macro_rules! wrap_unwrap_enum {
    ($enum:ident::$variant:ident($variant_ty:ident)) => {
        impl TryFrom<$enum> for $variant_ty {
            type Error = ();
            fn try_from(x: $enum) -> Result<Self, Self::Error> {
                match x {
                    $enum::$variant(x) => Ok(x),
                    _ => Err(()),
                }
            }
        }

        impl From<$variant_ty> for $enum {
            fn from(x: $variant_ty) -> Self {
                $enum::$variant(x)
            }
        }
    };
}

wrap_unwrap_enum!(ItemId::Fun(FunDeclId));
wrap_unwrap_enum!(ItemId::Global(GlobalDeclId));
wrap_unwrap_enum!(ItemId::Type(TypeDeclId));
wrap_unwrap_enum!(ItemId::TraitDecl(TraitDeclId));
wrap_unwrap_enum!(ItemId::TraitImpl(TraitImplId));
wrap_unwrap_enum!(AssocItemId::Type(AssocTypeId));
wrap_unwrap_enum!(AssocItemId::Method(TraitMethodId));
wrap_unwrap_enum!(AssocItemId::Const(AssocConstId));

impl TryFrom<ItemId> for FunId {
    type Error = ();
    fn try_from(x: ItemId) -> Result<Self, Self::Error> {
        Ok(FunId::Regular(x.try_into()?))
    }
}
impl From<FunDeclId> for FunId {
    fn from(id: FunDeclId) -> Self {
        Self::Regular(id)
    }
}
impl From<FunDeclId> for FnPtrKind {
    fn from(id: FunDeclId) -> Self {
        Self::Fun(id.into())
    }
}
impl From<FunId> for FnPtrKind {
    fn from(id: FunId) -> Self {
        Self::Fun(id)
    }
}
