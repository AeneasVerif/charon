use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA};
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};

use crate::ast::*;
use crate::ids::IndexVec;
use crate::utils::serialize_map_to_array::SeqHashMapToArray;

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
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[serde_state(state_implements = DedupSerializerState)]
pub struct TypeDecl {
    pub def_id: TypeDeclId,
    /// Meta information associated with the item.
    pub item_meta: ItemMeta,
    pub generics: GenericParams,
    /// The context of the type: distinguishes top-level items from closure-related items etc.
    pub src: TypeSource,
    /// The type kind: enum, struct, or opaque.
    pub kind: TypeDeclKind,
    /// The layout of the type for each target. Information may be partial because of generics or
    /// dynamically-sized types. If we cannot compute a layout, the target has no entry.
    #[serde(with = "SeqHashMapToArray::<TargetTriple, Layout>")]
    pub layout: SeqHashMap<TargetTriple, Layout>,
    /// The metadata associated with a pointer to the type.
    pub ptr_metadata: PtrMetadata,
}

generate_index_type!(VariantId, "Variant");
generate_index_type!(FieldId, "Field");

#[derive(
    Debug,
    Clone,
    EnumIsA,
    EnumAsGetters,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub enum TypeDeclKind {
    Struct(IndexVec<FieldId, Field>),
    Enum(IndexVec<VariantId, Variant>),
    Union(IndexVec<FieldId, Field>),
    /// An opaque type.
    ///
    /// Either a local type marked as opaque, or an external type.
    Opaque,
    /// An alias to another type. This only shows up in the top-level list of items, as rustc
    /// inlines uses of type aliases everywhere else.
    Alias(Ty),
    /// Used if an error happened during the extraction, and we don't panic
    /// on error.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("TDeclError"))]
    Error(String),
}

#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[serde_state(stateless)]
pub struct Variant {
    pub id: VariantId,
    pub span: Span,
    pub attr_info: AttrInfo,
    #[cfg_attr(feature = "charon_on_charon", charon::rename("variant_name"))]
    pub name: String,
    #[serde_state(stateful)]
    pub fields: IndexVec<FieldId, Field>,
    /// The discriminant value outputted by `std::mem::discriminant` for this variant. This can be
    /// different than the value stored in memory (called `tag`); that one is described by
    /// [`Discriminator`] and [`VariantLayout::tagger`].
    pub discriminant: Literal,
}

#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[serde_state(stateless)]
pub struct Field {
    pub span: Span,
    pub attr_info: AttrInfo,
    #[cfg_attr(feature = "charon_on_charon", charon::rename("field_name"))]
    pub name: String,
    /// Whether this field is positional, as in a tuple struct, tuple variant, or closure. If so,
    /// its name is based on its position, such as `_0`; otherwise, it is a user-provided name.
    pub is_positional: bool,
    #[cfg_attr(feature = "charon_on_charon", charon::rename("field_ty"))]
    #[serde_state(stateful)]
    pub ty: Ty,
}

/// The metadata stored in a pointer. That's the information stored in pointers alongside
/// their address. It's empty for `Sized` types, and interesting for unsized
/// aka dynamically-sized types.
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
#[serde_state(default_state = ())]
pub enum PtrMetadata {
    /// Types that need no metadata, namely `T: Sized` types.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("NoMetadata"))]
    None,
    /// Metadata for `[T]` and `str`, and user-defined types
    /// that directly or indirectly contain one of the two.
    /// Of type `usize`.
    /// Notably, length for `[T]` denotes the number of elements in the slice.
    /// While for `str` it denotes the number of bytes in the string.
    Length,
    /// Metadata for `dyn Trait`, referring to the vtable struct. Has type `&'static vtable`
    VTable(TypeDeclRef),
    /// Unknown due to generics, but will inherit from the given type.
    /// This is consistent with `<Ty as Pointee>::Metadata`.
    /// Of type `TyKind::Metadata(Ty)`.
    InheritFrom(Ty),
}

/// Where a given type came from.
#[derive(
    Debug,
    Clone,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
    EnumIsA,
    EnumAsGetters,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_suffix("Type"))]
pub enum TypeSource {
    /// A normal type declaration.
    Normal,
    /// The struct that carries the captured variables of a closure.
    Closure { info: ClosureInfo },
    /// Defines the vtable struct for a trait.
    VTable {
        /// The `dyn Trait` predicate implemented by this vtable.
        dyn_predicate: DynPredicate,
        /// Record what each vtable field means.
        field_map: IndexVec<FieldId, VTableField>,
        /// For each implied clause that is also a supertrait clause, records which field of the
        /// vtable corresponds to it.
        supertrait_map: IndexVec<TraitClauseId, Option<FieldId>>,
    },
    /// A type declaration synthesised for a builtin type.
    Builtin(BuiltinTy),
}

#[derive(
    Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo, PartialEq, Eq,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("VTable"))]
pub enum VTableField {
    Size,
    Align,
    Drop,
    Method(TraitMethodId),
    SuperTrait(TraitClauseId),
}

/// Additional information for closures.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub struct ClosureInfo {
    #[serde_state(stateless)]
    pub kind: ClosureKind,
    /// The `FnOnce` implementation of this closure -- always exists.
    pub fn_once_impl: RegionBinder<TraitImplRef>,
    /// The `FnMut` implementation of this closure, if any.
    pub fn_mut_impl: Option<RegionBinder<TraitImplRef>>,
    /// The `Fn` implementation of this closure, if any.
    pub fn_impl: Option<RegionBinder<TraitImplRef>>,
    /// The signature of the function that this closure represents.
    pub signature: RegionBinder<FunSig>,
}

#[derive(
    Debug,
    Copy,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

impl TypeDecl {
    pub fn get_field(&self, variant: Option<VariantId>, field: FieldId) -> Option<&Field> {
        let fields = match &self.kind {
            TypeDeclKind::Struct(fields) | TypeDeclKind::Union(fields) => fields,
            TypeDeclKind::Enum(variants) => &variants[variant.unwrap()].fields,
            _ => return None,
        };
        fields.get(field)
    }

    pub fn get_field_by_name(
        &self,
        variant: Option<VariantId>,
        field_name: &str,
    ) -> Option<(FieldId, &Field)> {
        let fields = match &self.kind {
            TypeDeclKind::Struct(fields) | TypeDeclKind::Union(fields) => fields,
            TypeDeclKind::Enum(variants) => &variants[variant.unwrap()].fields,
            _ => return None,
        };
        fields
            .iter_enumerated()
            .find(|(_, field)| field.name == field_name)
    }
}

impl Variant {
    /// The new name for this variant, as suggested by the `#[charon::rename]` and
    /// `#[charon::variants_prefix]` attributes.
    pub fn renamed_name(&self) -> &str {
        self.attr_info
            .rename
            .as_deref()
            .unwrap_or(self.name.as_ref())
    }

    /// Whether this variant has a `#[charon::opaque]` annotation.
    pub fn is_opaque(&self) -> bool {
        self.attr_info
            .attributes
            .iter()
            .any(|attr| attr.is_opaque())
    }
}

impl Field {
    /// The new name for this field, as suggested by the `#[charon::rename]` attribute.
    pub fn renamed_name(&self) -> &str {
        self.attr_info.rename.as_deref().unwrap_or(&self.name)
    }

    /// Whether this field has a `#[charon::opaque]` annotation.
    pub fn is_opaque(&self) -> bool {
        self.attr_info
            .attributes
            .iter()
            .any(|attr| attr.is_opaque())
    }
}

impl ClosureKind {
    // pub fn trait_name(self) -> &'static str {}
    pub fn method_name(self) -> &'static str {
        match self {
            ClosureKind::FnOnce => "call_once",
            ClosureKind::FnMut => "call_mut",
            ClosureKind::Fn => "call",
        }
    }
}

impl PtrMetadata {
    pub fn into_type(self) -> Ty {
        match self {
            PtrMetadata::None => Ty::mk_unit(),
            PtrMetadata::Length => Ty::mk_usize(),
            PtrMetadata::VTable(type_decl_ref) => Ty::new(TyKind::Ref(
                Region::Static,
                Ty::new(TyKind::Adt(type_decl_ref)),
                RefKind::Shared,
            )),
            PtrMetadata::InheritFrom(ty) => Ty::new(TyKind::PtrMetadata(ty)),
        }
    }
}
