//! The layout of types.
use crate::ast::*;
use crate::ids::IndexVec;
use crate::utils::serialize_map_to_array::SeqHashMapToArray;
use derive_generic_visitor::*;
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};

pub type ByteCount = u64;

/// Type layout information.
///
/// Does not include information about niches.
/// If the type does not have a fully known layout (e.g. it is ?Sized)
/// some of the layout parts are not available.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct Layout {
    /// The size of the type in bytes.
    pub size: SizeExpr,
    /// The alignment, in bytes.
    pub align: SizeExpr,
    /// Decision tree that determines the active variant by reading memory. Only `Some` for enums.
    pub discriminator: Option<Discriminator>,
    /// Whether the type is uninhabited, i.e. has any valid value at all.
    /// Note that uninhabited types can have arbitrary layouts: `(u32, !)` has space for the `u32`
    /// and `enum E2 { A, B(!), C(i32, !) }` may have space for a discriminant.
    pub uninhabited: bool,
    /// Map from `VariantId` to the corresponding field layouts. Some variants don't have a
    /// meaningful layout due to being uninhabited (though an uninhabited variant may have a
    /// layout). Structs and unions are modeled as having exactly one variant.
    pub variant_layouts: IndexVec<VariantId, Option<VariantLayout>>,
    /// The representation options of this type declaration as annotated by the user.
    #[serde_state(stateless)]
    pub repr: ReprOptions,
}

/// Simplified layout of a single variant.
///
/// Maps fields to their offset within the layout.
#[derive(Debug, Default, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct VariantLayout {
    /// The offset of each field.
    pub field_offsets: IndexVec<FieldId, OffsetExpr>,
    /// Whether the variant is uninhabited, i.e. has any valid possible value.
    /// Note that uninhabited types can have arbitrary layouts.
    pub uninhabited: bool,
    /// How to write the tag when constructing this variant. Each entry means: write `value` at
    /// byte `offset`. Mirrors MiniRust's `Variant::tagger`.
    #[serde_state(stateless)]
    pub tagger: Vec<(ByteCount, ScalarValue)>,
}

/// Decision tree used to determine the active variant by reading memory. Mirrors MiniRust's
/// `Discriminator`.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[serde_state(state_implements = DedupSerializerState)]
pub enum Discriminator {
    /// The variant is known.
    Known(VariantId),
    /// No valid variant (e.g., invalid tag value).
    Invalid,
    /// Branch on an integer value read from memory at `offset`.
    Branch {
        /// Byte offset to read from.
        offset: OffsetExpr,
        /// Integer type to read.
        #[serde_state(stateless)]
        int_ty: IntegerTy,
        /// If the integer is in one of these ranges, continue with the given `Discriminator`. The
        /// ranges are sorted.
        children: Vec<(std::ops::RangeInclusive<ScalarValue>, Discriminator)>,
        /// Fallback if no range in `children` matches.
        fallback: Box<Discriminator>,
    },
}

/// An expression denoting a size in bytes.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct SizeExpr {
    /// The guarantees about this size that can be relied on according to the Rust Reference.
    pub guarantee: Option<SizeGuarantee>,
    /// The size chosen by this rustc run. `None` for unsized types.
    pub chosen: Option<ByteCount>,
}

/// An expression denoting an offset in bytes.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct OffsetExpr {
    /// The guarantees about this offset that can be relied on according to the Rust Reference.
    pub guarantee: Option<OffsetGuarantee>,
    /// The offset chosen by this rustc run. `None` for unsized fields.
    pub chosen: Option<ByteCount>,
}

impl SizeExpr {
    pub fn new(chosen: impl Into<Option<ByteCount>>) -> Self {
        Self {
            guarantee: None,
            chosen: chosen.into(),
        }
    }
}

impl OffsetExpr {
    pub fn new(chosen: impl Into<Option<ByteCount>>) -> Self {
        Self {
            guarantee: None,
            chosen: chosen.into(),
        }
    }
}

/// The representation options as annotated by the user.
///
/// NOTE: This does not include less common/unstable representations such as `#[repr(simd)]`
/// or the compiler internal `#[repr(linear)]`. Similarly, enum discriminant representations
/// are encoded in [`Variant::discriminant`] and [`Discriminator`] instead.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReprOptions {
    pub repr_algo: ReprAlgorithm,
    pub align_modif: Option<AlignmentModifier>,
    pub transparent: bool,
    /// The type supplied to `repr(..)`, if any.
    pub explicit_discr_type: Option<LiteralTy>,
}

/// Describes which layout algorithm is used for representing the corresponding type.
/// Depends on the `#[repr(...)]` used.
#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReprAlgorithm {
    /// The default layout algorithm. Used without an explicit `ŗepr` or for `repr(Rust)`.
    #[default]
    Rust,
    /// The C layout algorithm as enforced by `repr(C)`.
    C,
}

/// Describes modifiers to the alignment and packing of the corresponding type.
/// Represents `repr(align(n))` and `repr(packed(n))`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum AlignmentModifier {
    Align(ByteCount),
    Pack(ByteCount),
}

#[derive(Clone, Drive, DriveMut, DriveTwo, SerializeState, DeserializeState)]
#[serde_state(stateless)]
pub struct TargetInfo {
    /// The pointer size of the target in bytes.
    pub target_pointer_size: ByteCount,
    /// Whether the target platform uses little endian byte order.
    pub is_little_endian: bool,
    /// The minimum size of a [`repr(C)`] enum.
    pub c_enum_smallest_repr_ty: IntTy,
    /// Alignments for primitive types.
    #[serde(with = "SeqHashMapToArray::<LiteralTy, ByteCount>")]
    pub primitive_alignments: SeqHashMap<LiteralTy, ByteCount>,
}

impl Layout {
    pub fn is_variant_uninhabited(&self, variant_id: VariantId) -> bool {
        self.variant_layouts[variant_id]
            .as_ref()
            .is_none_or(|v| v.uninhabited)
    }

    pub fn is_c_repr(&self) -> bool {
        self.repr.repr_algo == ReprAlgorithm::C
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum DiscriminantReadError {
    /// We read an uninitialized byte.
    UninitByte,
    /// We reached an invalid discriminant state.
    InvalidDiscriminant,
}

impl Discriminator {
    /// Make a trivial discriminator that always returns the given variant id.
    pub fn trivial(variant_id: VariantId) -> Self {
        Self::Known(variant_id)
    }

    /// Read a discriminant from memory. The `read` function simulates reading an integer of the
    /// given type at the given byte offset from memory and can return `UninitByte` if the byte
    /// could not be read.
    pub fn read_discriminant(
        &self,
        read: impl Fn(ByteCount, IntegerTy) -> Result<ScalarValue, DiscriminantReadError> + Copy,
    ) -> Result<VariantId, DiscriminantReadError> {
        match self {
            Discriminator::Known(id) => Ok(*id),
            Discriminator::Invalid => Err(DiscriminantReadError::InvalidDiscriminant),
            Discriminator::Branch {
                offset,
                int_ty,
                fallback,
                children,
            } => {
                let offset = offset
                    .chosen
                    .expect("a discriminator must have a concrete offset");
                let val = read(offset, *int_ty)?;
                for (range, child) in children {
                    if range.contains(&val) {
                        return child.read_discriminant(read);
                    }
                }
                fallback.read_discriminant(read)
            }
        }
    }
}

impl ReprOptions {
    /// Whether this representation options guarantee a fixed
    /// field ordering for the type.
    ///
    /// Since we don't support `repr(simd)` or `repr(linear)` yet, this is
    /// the case if it's either `repr(C)` or an explicit discriminant type for
    /// an enum with fields (if it doesn't have fields, this obviously doesn't matter anyway).
    ///
    /// Cf. <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.c.struct>
    /// and <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.primitive.adt>.
    pub fn guarantees_fixed_field_order(&self) -> bool {
        self.repr_algo == ReprAlgorithm::C || self.explicit_discr_type.is_some()
    }
}

impl IntTy {
    /// Important: this returns the target byte count for the types.
    /// Must not be used for host types from rustc.
    pub fn target_size(&self, ptr_size: ByteCount) -> usize {
        match self {
            IntTy::Isize => ptr_size as usize,
            IntTy::I8 => size_of::<i8>(),
            IntTy::I16 => size_of::<i16>(),
            IntTy::I32 => size_of::<i32>(),
            IntTy::I64 => size_of::<i64>(),
            IntTy::I128 => size_of::<i128>(),
        }
    }
}
impl UIntTy {
    /// Important: this returns the target byte count for the types.
    /// Must not be used for host types from rustc.
    pub fn target_size(&self, ptr_size: ByteCount) -> usize {
        match self {
            UIntTy::Usize => ptr_size as usize,
            UIntTy::U8 => size_of::<u8>(),
            UIntTy::U16 => size_of::<u16>(),
            UIntTy::U32 => size_of::<u32>(),
            UIntTy::U64 => size_of::<u64>(),
            UIntTy::U128 => size_of::<u128>(),
        }
    }
}
impl FloatTy {
    /// Important: this returns the target byte count for the types.
    /// Must not be used for host types from rustc.
    pub fn target_size(&self) -> usize {
        match self {
            FloatTy::F16 => size_of::<u16>(),
            FloatTy::F32 => size_of::<u32>(),
            FloatTy::F64 => size_of::<u64>(),
            FloatTy::F128 => size_of::<u128>(),
        }
    }
}
