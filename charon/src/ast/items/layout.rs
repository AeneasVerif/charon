//! The layout of types.
use crate::ast::*;
use crate::ids::IndexVec;
use crate::utils::serialize_map_to_array::SeqHashMapToArray;
use derive_generic_visitor::*;
use itertools::Itertools;
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
    pub size: Size,
    /// The alignment, in bytes.
    pub align: Size,
    /// Decision tree that determines the active variant by reading memory. Only `Some` for enums.
    pub discriminator: Option<Discriminator>,
    /// Whether the type has any valid value.
    /// Note that uninhabited types can have arbitrary layouts: `(u32, !)` has space for the `u32`
    /// and `enum E2 { A, B(!), C(i32, !) }` may have space for a discriminant.
    pub inhabited: InhabitedPredicate,
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
    /// Whether the variant has any valid possible value.
    /// Note that uninhabited types can have arbitrary layouts.
    pub inhabited: InhabitedPredicate,
    /// How to write the tag when constructing this variant. Each entry means: write `value` at
    /// byte `offset`. Mirrors MiniRust's `Variant::tagger`.
    #[serde_state(stateless)]
    pub tagger: Vec<(ByteCount, IntegerValue)>,
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
        children: Vec<(std::ops::RangeInclusive<IntegerValue>, Discriminator)>,
        /// Fallback if no range in `children` matches.
        fallback: Box<Discriminator>,
    },
}

/// An expression denoting a size in bytes.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct Size {
    /// The size chosen by this rustc run. For sized types, this is a plain integer. For unsized
    /// types, this is an expression describing how to compute this size based on the values found
    /// in the pointer metadata.
    pub chosen: SizeExpr,
    /// The guarantees about this size that can be relied on according to the Rust Reference.
    pub guarantee: Option<SizeExpr>,
}

/// An expression denoting an offset in bytes.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct OffsetExpr {
    /// The guarantees about this offset that can be relied on according to the Rust Reference.
    pub guarantee: Option<OffsetGuarantee>,
    /// The offset chosen by this rustc run. `None` for unsized fields.
    pub chosen: Option<ByteCount>,
}

impl Size {
    pub fn new(chosen: ByteCount) -> Self {
        Self::from_expr(SizeExprKind::from_usize(u128::from(chosen)).into_expr())
    }

    pub fn from_expr(chosen: SizeExpr) -> Self {
        Self {
            chosen,
            guarantee: None,
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

/// Represents whether a type or variant is inhabited. Like rustc's `InhabitedPredicate`, this can
/// depend on generic parameters and constant values.
#[derive(
    Debug, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
#[serde_state(state_implements = DedupSerializerState)]
pub struct InhabitedPredicate(pub HashConsed<InhabitedPredicateKind>);

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
#[cfg_attr(
    feature = "charon_on_charon",
    charon::variants_prefix("InhabitedPredicate")
)]
pub enum InhabitedPredicateKind {
    True,
    False,
    /// Inhabited when this constant is zero.
    ConstIsZero(ConstantExpr),
    /// Inhabited when this generic type is inhabited.
    GenericType(Ty),
    And(Vec<InhabitedPredicate>),
    Or(Vec<InhabitedPredicate>),
}

impl InhabitedPredicate {
    pub fn new(kind: InhabitedPredicateKind) -> Self {
        Self(HashConsed::new(kind))
    }

    pub fn kind(&self) -> &InhabitedPredicateKind {
        self.0.inner()
    }

    pub fn with_kind_mut<R>(&mut self, f: impl FnOnce(&mut InhabitedPredicateKind) -> R) -> R {
        self.0.with_inner_mut(f)
    }

    pub fn mk_true() -> Self {
        InhabitedPredicateKind::True.into_pred()
    }

    pub fn mk_false() -> Self {
        InhabitedPredicateKind::False.into_pred()
    }

    pub fn always_true(&self) -> bool {
        matches!(self.kind(), InhabitedPredicateKind::True)
    }

    pub fn always_false(&self) -> bool {
        matches!(self.kind(), InhabitedPredicateKind::False)
    }

    pub fn is_known(&self) -> bool {
        self.always_true() || self.always_false()
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self.kind() {
            InhabitedPredicateKind::True => Some(true),
            InhabitedPredicateKind::False => Some(false),
            _ => None,
        }
    }

    pub fn normalize(mut self, krate: &TranslatedCrate, for_target: Option<&TargetTriple>) -> Self {
        #[derive(Visitor)]
        struct NormalizeInhabitedPredicate<'a> {
            krate: &'a TranslatedCrate,
            for_target: Option<&'a TargetTriple>,
        }

        fn fold_concrete_values(
            predicates: &mut Vec<InhabitedPredicate>,
            f: impl Fn(bool, bool) -> bool,
        ) -> Option<bool> {
            predicates
                .extract_if(.., |pred| pred.is_known())
                .map(|pred| pred.as_bool().unwrap())
                .reduce(f)
        }

        impl VisitAstMut for NormalizeInhabitedPredicate<'_> {
            fn exit_inhabited_predicate_kind(&mut self, pred: &mut InhabitedPredicateKind) {
                *pred = match pred {
                    InhabitedPredicateKind::True | InhabitedPredicateKind::False => return,
                    InhabitedPredicateKind::ConstIsZero(value) => {
                        if let Some(value) = value.as_usize_literal() {
                            if value == 0 {
                                InhabitedPredicateKind::True
                            } else {
                                InhabitedPredicateKind::False
                            }
                        } else {
                            return;
                        }
                    }
                    InhabitedPredicateKind::GenericType(ty) => {
                        let mut new = ty.inhabited_predicate(self.krate, self.for_target);
                        if let InhabitedPredicateKind::GenericType(new_ty) = new.kind()
                            && new_ty == ty
                        {
                            return;
                        }
                        self.visit(&mut new);
                        new.kind().clone()
                    }
                    InhabitedPredicateKind::And(predicates) => {
                        for pred in std::mem::take(predicates) {
                            match pred.kind() {
                                InhabitedPredicateKind::And(nested) => {
                                    predicates.extend(nested.iter().cloned())
                                }
                                _ => predicates.push(pred),
                            }
                        }
                        if let Some(value) = fold_concrete_values(predicates, |x, y| x && y)
                            && !value
                        {
                            InhabitedPredicateKind::False
                        } else if predicates.is_empty() {
                            InhabitedPredicateKind::True
                        } else if predicates.len() == 1 {
                            predicates.pop().unwrap().kind().clone()
                        } else {
                            return;
                        }
                    }
                    InhabitedPredicateKind::Or(predicates) => {
                        for pred in std::mem::take(predicates) {
                            match pred.kind() {
                                InhabitedPredicateKind::Or(nested) => {
                                    predicates.extend(nested.iter().cloned())
                                }
                                _ => predicates.push(pred),
                            }
                        }
                        if let Some(value) = fold_concrete_values(predicates, |x, y| x || y)
                            && value
                        {
                            InhabitedPredicateKind::True
                        } else if predicates.is_empty() {
                            InhabitedPredicateKind::False
                        } else if predicates.len() == 1 {
                            predicates.pop().unwrap().kind().clone()
                        } else {
                            return;
                        }
                    }
                };
            }
        }

        NormalizeInhabitedPredicate { krate, for_target }.visit(&mut self);
        self
    }
}

impl InhabitedPredicateKind {
    pub fn into_pred(self) -> InhabitedPredicate {
        InhabitedPredicate::new(self)
    }
}

impl Ty {
    pub fn inhabited_predicate(
        &self,
        krate: &TranslatedCrate,
        for_target: Option<&TargetTriple>,
    ) -> InhabitedPredicate {
        match self.kind() {
            TyKind::Never => InhabitedPredicate::mk_false(),
            TyKind::Array(ty, len, _) => match len.as_usize_literal() {
                Some(0) => InhabitedPredicate::mk_true(),
                Some(_) => ty.inhabited_predicate(krate, for_target),
                None => InhabitedPredicateKind::Or(vec![
                    InhabitedPredicateKind::ConstIsZero(len.clone()).into_pred(),
                    ty.inhabited_predicate(krate, for_target),
                ])
                .into_pred(),
            },
            TyKind::Adt(ty_ref)
                if let Some(decl) = krate.type_decls.get(ty_ref.id)
                    && let Some(layout) = if let Some(target) = for_target {
                        decl.layout.get(target)
                    } else {
                        decl.layout.values().exactly_one().ok()
                    } =>
            {
                layout.inhabited.clone().substitute(&ty_ref.generics)
            }
            TyKind::TypeVar(_) | TyKind::TraitType(..) | TyKind::Adt(_) => {
                InhabitedPredicateKind::GenericType(self.clone()).into_pred()
            }
            TyKind::Scalar(_)
            | TyKind::Slice(..)
            | TyKind::Ref(..)
            | TyKind::RawPtr(..)
            | TyKind::FnDef(..)
            | TyKind::FnPtr(..)
            | TyKind::DynTrait(..)
            | TyKind::Pattern(..)
            | TyKind::PtrMetadata(..)
            | TyKind::Error(_) => InhabitedPredicate::mk_true(),
        }
    }
}

impl Default for InhabitedPredicate {
    fn default() -> Self {
        Self::mk_true()
    }
}

impl std::ops::Deref for InhabitedPredicate {
    type Target = InhabitedPredicateKind;

    fn deref(&self) -> &Self::Target {
        self.kind()
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
    pub explicit_discr_type: Option<IntegerTy>,
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
    #[serde(with = "SeqHashMapToArray::<ScalarTy, ByteCount>")]
    pub primitive_alignments: SeqHashMap<ScalarTy, ByteCount>,
}

impl Layout {
    pub fn is_variant_always_uninhabited(&self, variant_id: VariantId) -> bool {
        self.variant_layouts[variant_id]
            .as_ref()
            .is_none_or(|layout| layout.inhabited.always_false())
    }

    pub fn is_variant_always_inhabited(&self, variant_id: VariantId) -> bool {
        self.variant_layouts[variant_id]
            .as_ref()
            .is_none_or(|layout| layout.inhabited.always_true())
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
        read: impl Fn(ByteCount, IntegerTy) -> Result<IntegerValue, DiscriminantReadError> + Copy,
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
