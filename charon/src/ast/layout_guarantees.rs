use std::{collections::HashMap, ops::AddAssign};

use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA, VariantName};
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};

use crate::{
    ast::{
        AlignmentModifier, BuiltinTy, ConstantExpr, ConstantExprKind, Field, FieldId,
        HashConsSerializerState, IntTy, IntegerTy, Layout, Literal, LiteralTy, ReprAlgorithm,
        ReprOptions, ScalarValue, TargetTriple, TranslatedCrate, Ty, TyKind, TyVisitable,
        TypeDeclKind, TypeDeclRef, TypeId, UIntTy, VariantId, VariantLayout,
    },
    ids::IndexVec,
};

/// Variables representing layout information from the context.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Var"))]
pub enum LayoutVar {
    /// The size of the whole type.
    Size,
    /// The alignment of the whole type.
    Align,
    /// The offset of the given field.
    FieldOffset(Option<VariantId>, FieldId),
}

/// Represents the guarantees we can get about offsets of fields.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    DriveTwo,
)]
pub enum OffsetGuarantee {
    /// Guaranteed to be at offset zero. This applies for `repr(transparent)` and in some  `repr(C)` cases.
    AtOffsetZero,
    /// The only guarantee is that it is aligned to the given expression.
    GuaranteedAlignment(Box<SizeExpr>),
    /// This offset has to be computed by the layout algorithm for C, taking into consideration the fields before.
    /// Must not be the first field, since that is [`OffsetGuarantee::AtOffsetZero`].
    ReprCField {
        /// If this is `None`, then the field is directly behind the tag.
        predecessor: Option<FieldId>,
        predecessor_size: LayoutValue,
        own_ty: Ty,
    },
}

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    DriveTwo,
)]
#[serde_state(state_implements = HashConsSerializerState)]
pub enum LayoutValue {
    #[cfg_attr(feature = "charon_on_charon", charon::rename("LayoutValueConstant"))]
    Constant(ConstantExpr),
    /// The size of the given type.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("ValueSizeOf"))]
    SizeOf(Ty),
    /// The alignment of the given type.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("ValueAlignOf"))]
    AlignOf(Ty),
    /// For a DST with `dyn Trait` metadata, this refers to the size found in the metadata.
    DynSize,
    /// For a DST with `dyn Trait` metadata, this refers to the alignment found in the metadata.
    DynAlign,
    /// For a DST with slice metadata, this refers to the length found in the metadata.
    SliceLength,
    /// The size of the default discriminant type for a target.
    TargetDiscrSize,
    /// The alignment of the default discriminant type for a target.
    TargetDiscrAlign,
}

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    DriveTwo,
)]
#[serde_state(state_implements = HashConsSerializerState)]
pub enum SizeExpr {
    #[serde_state(stateless)]
    #[cfg_attr(feature = "charon_on_charon", charon::rename("SizeVariable"))]
    Var(LayoutVar),
    #[cfg_attr(feature = "charon_on_charon", charon::rename("SizeValue"))]
    Val(LayoutValue),
    Max(Vec<SizeExpr>),
    Min(Vec<SizeExpr>),
    Plus(Box<SizeExpr>, Box<SizeExpr>),
    Scale(Box<SizeExpr>, ConstantExpr),
    /// The next multiple of `target_align` from `base`.
    AlignTo {
        base: Box<SizeExpr>,
        target_align: Box<SizeExpr>,
    },
    /// A size expression that changes its value based on whether an argument type is inhabited.
    IfInhabited {
        ty: Ty,
        then_size: Box<SizeExpr>,
        else_size: Box<SizeExpr>,
    },
}

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    DriveTwo,
)]
#[serde_state(state_implements = HashConsSerializerState)]
pub enum SizeExprBound {
    ExactEq(SizeExpr),
    LowerBound(SizeExpr),
}

impl SizeExprBound {
    pub fn map<F: Fn(SizeExpr) -> SizeExpr>(self, f: F) -> Self {
        match self {
            Self::ExactEq(size_expr) => Self::ExactEq(f(size_expr)),
            Self::LowerBound(size_expr) => Self::LowerBound(f(size_expr)),
        }
    }

    pub fn map_mut<F: Fn(&mut SizeExpr)>(&mut self, f: F) {
        match self {
            Self::ExactEq(size_expr) | Self::LowerBound(size_expr) => f(size_expr),
        }
    }

    pub fn comb<F: Fn(SizeExpr, SizeExpr) -> SizeExpr>(self, other: Self, f: F) -> Self {
        match (self, other) {
            (Self::ExactEq(size_expr1), Self::ExactEq(size_expr2)) => {
                Self::ExactEq(f(size_expr1, size_expr2))
            }
            (Self::ExactEq(size_expr1), Self::LowerBound(size_expr2))
            | (Self::LowerBound(size_expr1), Self::ExactEq(size_expr2))
            | (Self::LowerBound(size_expr1), Self::LowerBound(size_expr2)) => {
                Self::LowerBound(f(size_expr1, size_expr2))
            }
        }
    }

    pub fn make(expr: SizeExpr, exact: bool) -> Self {
        if exact {
            Self::ExactEq(expr)
        } else {
            Self::LowerBound(expr)
        }
    }

    pub fn inner(&self) -> &SizeExpr {
        match self {
            Self::ExactEq(size_expr) | Self::LowerBound(size_expr) => size_expr,
        }
    }

    pub fn inner_mut(&mut self) -> &mut SizeExpr {
        match self {
            Self::ExactEq(size_expr) | Self::LowerBound(size_expr) => size_expr,
        }
    }

    pub fn take(self) -> SizeExpr {
        match self {
            Self::ExactEq(size_expr) | Self::LowerBound(size_expr) => size_expr,
        }
    }

    pub fn add_exact_info(self, exact: bool) -> Self {
        match self {
            Self::ExactEq(size_expr) if exact => Self::ExactEq(size_expr),
            _ => Self::LowerBound(self.take()),
        }
    }

    pub fn update<F: FnMut(&mut SizeExpr, bool) -> bool>(&mut self, mut f: F) {
        let old_exact = self.is_exact_eq();
        let new_exact = f(self.inner_mut(), old_exact);
        // FIXME: Is there some sound unsafe code to make this possible without the clone?
        *self = Self::make(self.inner().clone(), old_exact && new_exact);
    }
}

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    DriveTwo,
)]
#[serde_state(state_implements = HashConsSerializerState)]
#[cfg_attr(
    feature = "charon_on_charon",
    charon::variants_prefix("OffsetGuarantee")
)]
pub enum OffsetGuarantees {
    Symbolic(Ty),
    Variants(IndexVec<VariantId, IndexVec<FieldId, OffsetGuarantee>>),
    Fields(IndexVec<FieldId, OffsetGuarantee>),
    None,
}

impl OffsetGuarantees {
    pub fn first_field(&self) -> Option<&OffsetGuarantee> {
        match self {
            Self::Variants(variants) => variants
                .get(VariantId::ZERO)
                .and_then(|fields| fields.get(FieldId::ZERO)),
            Self::Fields(fields) => fields.get(FieldId::ZERO),
            _ => None,
        }
    }

    pub fn first_field_mut(&mut self) -> Option<&mut OffsetGuarantee> {
        match self {
            Self::Variants(variants) => variants
                .get_mut(VariantId::ZERO)
                .and_then(|fields| fields.get_mut(FieldId::ZERO)),
            Self::Fields(fields) => fields.get_mut(FieldId::ZERO),
            _ => None,
        }
    }

    pub fn get_variants(
        self,
        expected_variants: Option<usize>,
        translated: &TranslatedCrate,
    ) -> Option<IndexVec<VariantId, IndexVec<FieldId, OffsetGuarantee>>> {
        match self {
            Self::Variants(variants_guarantees) => Some(variants_guarantees),
            Self::None if expected_variants.is_some() => Some(
                (0..expected_variants.unwrap())
                    .map(|_| vec![].into())
                    .collect(),
            ),
            Self::Symbolic(ty) => {
                let guarantees_for_ty = LayoutGuarantees::for_ty(&ty, translated)?;
                if let OffsetGuarantees::Symbolic(ty2) = &guarantees_for_ty.offsets
                    && ty == *ty2
                {
                    // Break cycles.
                    None
                } else {
                    guarantees_for_ty
                        .offsets
                        .get_variants(expected_variants, translated)
                }
            }
            Self::Fields(fields) => Some(vec![fields].into()),
            _ => None,
        }
    }

    pub fn from_layout(layout: &IndexVec<VariantId, Option<VariantLayout>>) -> Self {
        let mut offsets = IndexVec::new();
        for variant_layout in layout.iter() {
            let fields: Option<IndexVec<FieldId, OffsetGuarantee>> =
                if let Some(variant_layout) = variant_layout {
                    variant_layout
                        .field_offsets
                        .iter()
                        .map(|offset| offset.guarantees.clone())
                        .collect()
                } else {
                    None
                };
            if let Some(fields) = fields {
                offsets.push(fields);
            } else {
                return Self::None;
            }
        }
        Self::Variants(offsets)
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
#[serde_state(state_implements = HashConsSerializerState)]
pub struct LayoutGuarantees {
    pub size: SizeExprBound,
    pub align: SizeExprBound,
    pub offsets: OffsetGuarantees,
}

impl LayoutValue {
    pub fn mk_address_size() -> Self {
        Self::SizeOf(Ty::mk_usize())
    }

    pub fn mk_address_size_for(
        translated: &TranslatedCrate,
        target: &TargetTriple,
    ) -> Option<Self> {
        translated
            .target_information
            .get(target)
            .map(|target_info| {
                Self::Constant(
                    ScalarValue::mk_usize(
                        target_info.target_pointer_size,
                        target_info.target_pointer_size,
                    )
                    .to_constant(),
                )
            })
    }

    pub fn make_primitive_align_for_target(
        ty: &LiteralTy,
        translated: &TranslatedCrate,
        target: &TargetTriple,
    ) -> Option<Self> {
        let target_info = translated.target_information.get(target)?;
        let align = target_info.primitive_alignments.get(ty)?;
        Some(Self::Constant(
            ScalarValue::mk_usize(target_info.target_pointer_size, *align).to_constant(),
        ))
    }

    pub fn of_ty(ty: &Ty, is_size: bool) -> Self {
        match ty.kind() {
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Builtin(BuiltinTy::Str),
                ..
            }) => {
                if is_size {
                    Self::SliceLength
                } else {
                    Self::AlignOf(Ty::new(TyKind::Literal(LiteralTy::UInt(UIntTy::U8))))
                }
            }
            TyKind::DynTrait(_) => {
                if is_size {
                    Self::DynSize
                } else {
                    Self::DynAlign
                }
            }
            TyKind::Slice(ty) => {
                if is_size {
                    Self::SliceLength
                } else {
                    Self::AlignOf(ty.clone())
                }
            }
            _ => {
                if is_size {
                    Self::SizeOf(ty.clone())
                } else {
                    Self::AlignOf(ty.clone())
                }
            }
        }
    }
}

impl Default for SizeExpr {
    fn default() -> Self {
        Self::Val(LayoutValue::Constant(ConstantExpr::mk_usize(
            ScalarValue::mk_zero_usize(),
        )))
    }
}

impl SizeExpr {
    pub fn mk_const_byte_count(bytes: u64) -> Self {
        Self::Val(LayoutValue::Constant(ConstantExpr {
            kind: ConstantExprKind::Literal(Literal::Scalar(ScalarValue::Unsigned(
                UIntTy::U64,
                bytes as u128,
            ))),
            ty: Ty::new(TyKind::Literal(LiteralTy::UInt(UIntTy::U64))),
        }))
    }

    pub fn is_constant(&self) -> Option<ConstantExpr> {
        match self {
            Self::Val(LayoutValue::Constant(c)) => Some(c.clone()),
            _ => None,
        }
    }

    pub fn realign(&mut self, align_to: Self) {
        match self {
            Self::AlignTo { target_align, .. } => **target_align = align_to,
            Self::Val(LayoutValue::Constant(ConstantExpr {
                kind: ConstantExprKind::Literal(Literal::Scalar(s)),
                ..
            })) if align_to.is_constant().is_some() => {
                let Some(ConstantExpr {
                    kind: ConstantExprKind::Literal(Literal::Scalar(align_to)),
                    ..
                }) = align_to.is_constant()
                else {
                    unreachable!()
                };
                let (ty, c) = s.as_unsigned().unwrap();
                let align_to = align_to.as_uint().unwrap();
                if !c.is_multiple_of(align_to) {
                    let aligned = c + align_to - (c % align_to);
                    *s = ScalarValue::from_bits(IntegerTy::Unsigned(*ty), aligned);
                }
            }
            _ => {
                *self = Self::AlignTo {
                    base: Box::new(self.clone()),
                    target_align: Box::new(align_to),
                }
            }
        }
    }

    pub fn unalign(self) -> Self {
        match self {
            SizeExpr::AlignTo { base, .. } => *base,
            _ => self,
        }
    }

    pub fn max(&mut self, rhs: Self) {
        if let Self::Max(elems) = self {
            if let Self::Max(rhs_max) = rhs {
                elems.extend(rhs_max);
            } else {
                elems.push(rhs);
            }
        } else {
            *self = Self::Max(vec![self.clone(), rhs]);
        }
    }
}

impl AddAssign for SizeExpr {
    fn add_assign(&mut self, rhs: SizeExpr) {
        *self = Self::Plus(Box::new(self.clone()), Box::new(rhs));
    }
}

impl LayoutGuarantees {
    pub fn one_zst() -> Self {
        Self {
            size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::Constant(
                ScalarValue::mk_zero_usize().to_constant(),
            ))),
            align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::Constant(
                ScalarValue::mk_one_usize().to_constant(),
            ))),
            offsets: OffsetGuarantees::None,
        }
    }

    /// Does not set field offsets.
    pub fn mk_concrete(size: ScalarValue, alignment: ScalarValue) -> Self {
        if size.is_multiple_of(&alignment) == Some(true) {
            Self {
                size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::Constant(
                    size.to_constant(),
                ))),
                align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::Constant(
                    alignment.to_constant(),
                ))),
                offsets: OffsetGuarantees::None,
            }
        } else {
            panic!(
                "Type size {} not a multiple of alignment {}!",
                size, alignment
            )
        }
    }

    /// Based on [https://doc.rust-lang.org/reference/type-layout.html#r-layout.array].
    pub fn mk_array(elem_ty: &Ty, elem_num: &ConstantExpr) -> Self {
        Self {
            size: SizeExprBound::ExactEq(SizeExpr::Scale(
                Box::new(SizeExpr::Val(LayoutValue::of_ty(elem_ty, true))),
                elem_num.clone(),
            )),
            align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(elem_ty, false))),
            offsets: OffsetGuarantees::None,
        }
    }

    /// This is consistent with [`rustc_middle::ty::Ty::primitive_size`].
    ///
    /// However, currently it ignores potential inconsistencies with regard to
    /// [https://doc.rust-lang.org/reference/type-layout.html#r-layout.primitive.size].
    pub fn mk_primitive(primitive: &LiteralTy) -> Self {
        let size = match primitive {
            LiteralTy::Int(IntTy::Isize) | LiteralTy::UInt(UIntTy::Usize) => {
                return Self {
                    size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::mk_address_size())),
                    align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::mk_address_size())),
                    offsets: OffsetGuarantees::None,
                };
            }
            LiteralTy::Int(int_ty) => int_ty.target_size(0),
            LiteralTy::UInt(uint_ty) => uint_ty.target_size(0),
            LiteralTy::Float(float_ty) => float_ty.target_size(),
            LiteralTy::Bool => 1,
            LiteralTy::Char => 4,
        };
        Self {
            size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::Constant(
                ScalarValue::from_unchecked_uint(UIntTy::Usize, size as u128).to_constant(),
            ))),
            align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::AlignOf(Ty::from(
                *primitive,
            )))),
            offsets: OffsetGuarantees::None,
        }
    }

    pub fn mk_symbolic(ty: Ty) -> Self {
        Self {
            size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(&ty, true))),
            align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(&ty, false))),
            offsets: OffsetGuarantees::Symbolic(ty),
        }
    }

    pub fn is_purely_symbolic(&self) -> bool {
        matches!(
            self,
            Self {
                size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::SizeOf(_))),
                align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::AlignOf(_))),
                offsets: OffsetGuarantees::Symbolic(_),
            }
        )
    }

    /// The layout of a pointer to `pointee`. Uses the symbolic size of meta-data.
    ///
    /// Based on [https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer.unsized].
    fn mk_ptr(pointee: &Ty, translated: &TranslatedCrate) -> Self {
        let meta = pointee.get_ptr_metadata(translated).into_type();
        // If we have no metadata, the pointer is exactly the address value.
        let exact = meta.is_unit();
        let ptr_size = LayoutValue::mk_address_size();
        let align = SizeExpr::Max(vec![
            SizeExpr::Val(ptr_size.clone()),
            SizeExpr::Val(LayoutValue::of_ty(&meta, true)),
        ]);
        let size = SizeExprBound::make(
            SizeExpr::AlignTo {
                base: Box::new(SizeExpr::Plus(
                    Box::new(SizeExpr::Val(ptr_size)),
                    Box::new(SizeExpr::Val(LayoutValue::of_ty(&meta, true))),
                )),
                target_align: Box::new(align.clone()),
            },
            exact,
        );
        Self {
            size,
            align: SizeExprBound::make(align, exact),
            // We have guarantee about the offsets of the pointer parts, especially since
            // the parts have no field IDs.
            offsets: OffsetGuarantees::None,
        }
    }

    /// Computes the layout of a fixed, but unordered sequence of elements of the given types.
    /// This covers the Rust representation of both tuples and structs.
    ///
    /// The returned [`LayoutGuarantees::offsets`] ignore the variant id and store the field
    /// offsets at index 0.
    pub fn mk_unordered_sequence<I>(
        fields: I,
        variant_id: Option<VariantId>,
        repr: Option<&ReprOptions>,
    ) -> Self
    where
        I: Iterator<Item = Ty>,
    {
        let mut size_max = Vec::new();
        let mut align_max = Vec::new();
        let mut field_offsets = IndexVec::new();
        let packed_align = if let Some(repr) = repr
            && let Some(AlignmentModifier::Pack(p)) = &repr.align_modif
        {
            Some(SizeExpr::Val(LayoutValue::Constant(
                ScalarValue::from_unchecked_uint(UIntTy::U64, *p as u128).to_constant(),
            )))
        } else {
            None
        };
        for (id, ty) in fields.enumerate() {
            let end_of_field = SizeExpr::Plus(
                Box::new(SizeExpr::Var(LayoutVar::FieldOffset(
                    variant_id,
                    FieldId::from_raw(id),
                ))),
                Box::new(SizeExpr::Val(LayoutValue::of_ty(&ty, true))),
            );
            size_max.push(end_of_field);
            align_max.push(SizeExpr::Val(LayoutValue::of_ty(&ty, false)));
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.alignment.packed-fields
            // and https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.rust.layout, point 2.
            let field_offset_guarantee = OffsetGuarantee::GuaranteedAlignment(Box::new(
                if let Some(packed) = &packed_align {
                    SizeExpr::Min(vec![
                        packed.clone(),
                        SizeExpr::Val(LayoutValue::of_ty(&ty, false)),
                    ])
                } else {
                    SizeExpr::Val(LayoutValue::of_ty(&ty, false))
                },
            ));
            field_offsets.push(field_offset_guarantee);
        }

        // An empty tuple is the unit type.
        // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.tuple.unit.
        if size_max.is_empty() && align_max.is_empty() {
            return Self::one_zst();
        }

        Self {
            // The size is the end of the last field, i.e. the max of field ends, aligned.
            // This implicitly follows from
            // https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.rust.layout.struct
            size: SizeExprBound::LowerBound(SizeExpr::AlignTo {
                base: Box::new(SizeExpr::Max(size_max)),
                target_align: Box::new(SizeExpr::Var(LayoutVar::Align)),
            }),
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.rust.layout, point 2.
            align: SizeExprBound::LowerBound(SizeExpr::Max(align_max)),
            offsets: OffsetGuarantees::Fields(field_offsets),
        }
    }

    /// This computes the repr(C) layout guarantees for a struct/variant with the given fields
    /// and tag layout.
    ///
    /// The returned [`LayoutGuarantees::offsets`] ignore the variant id and store the field
    /// offsets at index 0.
    pub fn mk_ordered_sequence_repr_c<I>(
        fields: I,
        variant_id: Option<VariantId>,
        prefix_tag_layout: Option<Self>,
    ) -> Self
    where
        I: Iterator<Item = Ty>,
    {
        let tag_exists = prefix_tag_layout.is_some();
        let mut align_max = Vec::new();
        let mut last_ty = None;
        // If there are no fields, the size will be just the tag or 0.
        let mut size = if let Some(tag_guarantees) = prefix_tag_layout {
            align_max.push(tag_guarantees.align.take());
            let size = tag_guarantees.size.take();
            if let SizeExpr::Val(LayoutValue::SizeOf(tag_ty)) = &size {
                last_ty = Some(tag_ty.clone());
            }
            size
        } else {
            SizeExpr::Val(LayoutValue::Constant(
                ScalarValue::mk_zero_usize().to_constant(),
            ))
        };
        let mut field_offsets = IndexVec::new();

        let mut peekable_fields = fields.enumerate().peekable();
        while let Some((id, ty)) = peekable_fields.next() {
            if peekable_fields.peek().is_none() {
                // Only the last field is relevant for the size here.
                size = SizeExpr::Plus(
                    Box::new(SizeExpr::Var(LayoutVar::FieldOffset(
                        variant_id,
                        FieldId::from_raw(id),
                    ))),
                    Box::new(SizeExpr::Val(LayoutValue::of_ty(&ty, true))),
                )
            }
            let field_align = SizeExpr::Val(LayoutValue::of_ty(&ty, false));
            align_max.push(field_align);
            if id == 0 {
                if tag_exists {
                    field_offsets.push(OffsetGuarantee::ReprCField {
                        predecessor: None,
                        predecessor_size: if let Some(ty) = last_ty {
                            LayoutValue::of_ty(&ty, true)
                        } else {
                            LayoutValue::TargetDiscrSize
                        },
                        own_ty: ty.clone(),
                    });
                } else {
                    field_offsets.push(OffsetGuarantee::AtOffsetZero);
                }
            } else {
                field_offsets.push(OffsetGuarantee::ReprCField {
                    predecessor: Some(FieldId::from_raw(id - 1)),
                    predecessor_size: LayoutValue::of_ty(&last_ty.unwrap(), true),
                    own_ty: ty.clone(),
                });
            }
            last_ty = Some(ty);
        }

        Self {
            size: SizeExprBound::ExactEq(SizeExpr::AlignTo {
                base: Box::new(size),
                target_align: Box::new(SizeExpr::Var(LayoutVar::Align)),
            }),
            align: SizeExprBound::ExactEq(SizeExpr::Max(align_max)),
            offsets: OffsetGuarantees::Fields(field_offsets),
        }
    }

    /// Generates the layout guarantees for a (tagged) union.
    /// NOTE: Assumes the type to be repr(C)!
    pub fn mk_tagged_union<V, F>(
        variants: V,
        tag_layout_guarantee: Option<Self>,
        translated: &TranslatedCrate,
        is_union: bool,
    ) -> Self
    where
        V: Iterator<Item = F>,
        F: Iterator<Item = Ty>,
    {
        let mut max_size = SizeExpr::Max(Vec::new());
        let mut max_align = SizeExpr::Max(Vec::new());
        let mut offsets = IndexVec::new();

        for (id, mut fields) in variants.enumerate() {
            // Unions don't have an actual structure, but a single field, which needs to be
            // handled as if it has the same repr annotation as the whole union.
            let variant_guarantees = if is_union {
                let mut guarantees =
                    Self::for_ty_inner(&fields.next().unwrap(), translated, true).unwrap();
                if let Some(first_field) = guarantees.offsets.first_field_mut() {
                    *first_field = OffsetGuarantee::AtOffsetZero;
                }
                guarantees
            } else {
                LayoutGuarantees::mk_ordered_sequence_repr_c(
                    fields,
                    Some(VariantId::from_raw(id)),
                    tag_layout_guarantee.clone(),
                )
            };
            max_size.max(variant_guarantees.size.take().unalign());
            max_align.max(variant_guarantees.align.take());
            let field_offsets = match variant_guarantees.offsets {
                OffsetGuarantees::Variants(mut variants) => variants.pop().unwrap(),
                OffsetGuarantees::Fields(fields) => fields,
                _ => IndexVec::new(),
            };
            offsets.push(field_offsets);
        }

        let size = SizeExprBound::ExactEq(SizeExpr::AlignTo {
            base: Box::new(max_size),
            target_align: Box::new(SizeExpr::Var(LayoutVar::Align)),
        });
        // Since we assume repr(C), the guarantees are exact.
        LayoutGuarantees {
            size,
            align: SizeExprBound::ExactEq(max_align),
            offsets: OffsetGuarantees::Variants(offsets),
        }
    }

    /// There must be at most one non-1-ZST field in the single variant.
    /// Based on https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.transparent
    fn mk_transparent_layout_guarantees(
        fields: &IndexVec<FieldId, Field>,
        translated: &TranslatedCrate,
    ) -> Option<LayoutGuarantees> {
        let mut non_one_zst_ty = None;
        let mut field_guarantees = IndexVec::new();
        for field in fields.iter() {
            let ty = &field.ty;
            let layout = LayoutGuarantees::for_ty(ty, translated)?;
            if layout != LayoutGuarantees::one_zst() {
                if non_one_zst_ty.is_some() {
                    return None; // More than one non-1-ZST field!
                }
                non_one_zst_ty = Some(ty.clone());
                if let SizeExprBound::ExactEq(align) = layout.align {
                    field_guarantees.push(OffsetGuarantee::GuaranteedAlignment(Box::new(align)));
                } else {
                    field_guarantees.push(OffsetGuarantee::GuaranteedAlignment(Box::new(
                        SizeExpr::Val(LayoutValue::AlignOf(ty.clone())),
                    )));
                }
            } else {
                field_guarantees.push(OffsetGuarantee::GuaranteedAlignment(Box::new(
                    SizeExpr::Val(LayoutValue::AlignOf(ty.clone())),
                )));
            }
        }

        if let Some(non_one_zst_ty) = non_one_zst_ty {
            let mut single_field_layout = LayoutGuarantees::mk_symbolic(non_one_zst_ty);
            single_field_layout.offsets = OffsetGuarantees::Fields(field_guarantees);
            Some(single_field_layout)
        } else {
            // If there is no non-1-ZST field, the type is equivalent to unit.
            Some(LayoutGuarantees::one_zst())
        }
    }

    /// Constructs the layout guarantees for the type declaration.
    #[tracing::instrument(skip(translated))]
    pub fn for_type_decl(
        td_kind: &TypeDeclKind,
        repr: &ReprOptions,
        translated: &TranslatedCrate,
    ) -> Option<Self> {
        match td_kind {
            TypeDeclKind::Struct(fields) => {
                if repr.transparent {
                    return Self::mk_transparent_layout_guarantees(fields, translated);
                }

                let fields = fields.iter().map(|field| field.ty.clone());

                if repr.repr_algo == ReprAlgorithm::C {
                    let repr_c_guarantees = Self::mk_ordered_sequence_repr_c(fields, None, None);
                    return Some(repr_c_guarantees);
                }

                let mut base_guarantees = Self::mk_unordered_sequence(fields, None, Some(repr));
                // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.align-packed
                match repr.align_modif {
                    Some(AlignmentModifier::Align(forced_align)) => {
                        base_guarantees.align.map_mut(|align| {
                            align.max(SizeExpr::Val(LayoutValue::Constant(
                                ScalarValue::from_unchecked_uint(UIntTy::U64, forced_align as u128)
                                    .to_constant(),
                            )))
                        });
                    }
                    Some(AlignmentModifier::Pack(n)) => {
                        base_guarantees.align = SizeExprBound::ExactEq(SizeExpr::Min(vec![
                            SizeExpr::Val(LayoutValue::Constant(
                                ScalarValue::from_unchecked_uint(UIntTy::U64, n as u128)
                                    .to_constant(),
                            )),
                            base_guarantees.align.take(),
                        ]));
                    }
                    _ => (),
                }
                Some(base_guarantees)
            }
            TypeDeclKind::Enum(variants) => {
                if repr.transparent {
                    debug_assert_eq!(variants.len(), 1);
                    let fields = &variants.iter().next()?.fields;
                    Self::mk_transparent_layout_guarantees(fields, translated)
                } else {
                    // An explicit discriminant type implies that the enum has also C representation.
                    // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.primitive.adt
                    // Also, both cases imply that the discriminant type is guaranteed to be either the specified
                    // type, or the default discriminant type for a target.
                    if repr.guarantees_fixed_field_order() {
                        let field_less = variants.iter().all(|variant| variant.fields.is_empty());

                        let discr_layout_guarantee =
                            if let Some(discr_ty) = &repr.explicit_discr_type {
                                Self::for_ty(discr_ty, translated).unwrap()
                            } else {
                                Self {
                                    size: SizeExprBound::ExactEq(SizeExpr::Val(
                                        LayoutValue::TargetDiscrSize,
                                    )),
                                    align: SizeExprBound::ExactEq(SizeExpr::Val(
                                        LayoutValue::TargetDiscrAlign,
                                    )),
                                    offsets: OffsetGuarantees::None,
                                }
                            };

                        if field_less {
                            // For field-less enums with a guaranteed discriminant type, the whole layout is exactly the type.
                            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.primitive.enum
                            Some(discr_layout_guarantee)
                        } else {
                            // For enums with fields and #[repr(C)], the whole layout is a tagged union with the
                            // specified discriminant and a union of each variant as a #[repr(C)] struct.
                            // See https://doc.rust-lang.org/reference/type-layout.html#primitive-representation-of-enums-with-fields
                            // and https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.c.adt
                            let variants = variants
                                .iter()
                                .map(|variant| variant.fields.iter().map(|field| field.ty.clone()));
                            Some(Self::mk_tagged_union(
                                variants,
                                Some(discr_layout_guarantee),
                                translated,
                                false,
                            ))
                        }
                    } else {
                        // We only know the most basic guarantees, i.e. fields being aligned,
                        // fields not overlapping inside each variant, and the alignment
                        // being at least the maximum of the alignment of any field.
                        // At the moment, we do not express any guarantees about niches
                        // and thus need to over-approximate by saying that the size
                        // and alignment do not mention the tag, in case it is niche-encoded.
                        // Nonetheless, we also have no guarantee about the tag type
                        // if it's not niche-encoded anyway, so we cannot get much better in general.
                        let mut max_size = SizeExpr::Max(Vec::new());
                        let mut max_align = SizeExpr::Max(Vec::new());
                        let mut offsets = IndexVec::new();

                        for (id, variant) in variants.iter_enumerated() {
                            let fields = variant.fields.iter().map(|field| field.ty.clone());
                            let variant_guarantees =
                                LayoutGuarantees::mk_unordered_sequence(fields, Some(id), None);
                            max_size.max(variant_guarantees.size.take().unalign());
                            max_align.max(variant_guarantees.align.take());

                            let field_offsets = match variant_guarantees.offsets {
                                OffsetGuarantees::Variants(mut variants) => variants.pop().unwrap(),
                                OffsetGuarantees::Fields(fields) => fields,
                                _ => IndexVec::new(),
                            };
                            offsets.push(field_offsets);
                        }

                        let size = SizeExprBound::LowerBound(SizeExpr::AlignTo {
                            base: Box::new(max_size),
                            target_align: Box::new(SizeExpr::Var(LayoutVar::Align)),
                        });
                        // Since we assume repr(C), the guarantees are exact.
                        Some(LayoutGuarantees {
                            size,
                            align: SizeExprBound::LowerBound(max_align),
                            offsets: OffsetGuarantees::Variants(offsets),
                        })
                    }
                }
            }
            TypeDeclKind::Union(fields) => {
                // We get no guarantees for non-`repr(C)` unions.
                // See https://doc.rust-lang.org/reference/types/union.html#r-type.union.layout
                if repr.repr_algo != ReprAlgorithm::C {
                    return None;
                }

                // The layout of a union is the max size and alignment among all its variants.
                // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.c.union.size-align
                let variants = fields
                    .iter()
                    .map(|field| Some(field.ty.clone()).into_iter());
                Some(Self::mk_tagged_union(variants, None, translated, true))
            }
            TypeDeclKind::Alias(ty) => Some(Self::mk_symbolic(ty.clone())),
            _ => None,
        }
    }

    pub fn from_layout(layout: &Layout) -> Self {
        Self {
            size: layout.size.guarantees.clone(),
            align: layout.align.guarantees.clone(),
            offsets: OffsetGuarantees::from_layout(&layout.variant_layouts),
        }
    }

    fn for_ty_inner(ty: &Ty, translated: &TranslatedCrate, force_repr_c: bool) -> Option<Self> {
        match ty.kind() {
            // True Adt's (i.e. structs and enums) should have layout guarantees stored in
            // the corresponding type declaration.
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Adt(type_decl_id),
                generics,
            }) => {
                if let Some(td) = translated.type_decls.get(*type_decl_id) {
                    let poly_guarantees = Self::from_layout(td.the_layout()?);
                    Some(poly_guarantees.substitute(generics))
                } else {
                    Some(Self::mk_symbolic(ty.clone()))
                }
            }
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Tuple,
                generics,
            }) => {
                if force_repr_c {
                    Some(Self::mk_ordered_sequence_repr_c(
                        generics.types.iter().cloned(),
                        None,
                        None,
                    ))
                } else {
                    Some(Self::mk_unordered_sequence(
                        generics.types.iter().cloned(),
                        None,
                        None,
                    ))
                }
            }
            TyKind::TypeVar(_) => Some(Self::mk_symbolic(ty.clone())),
            TyKind::Literal(literal_ty) => Some(Self::mk_primitive(literal_ty)),
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Builtin(BuiltinTy::Box),
                generics,
            }) => Some(Self::mk_ptr(generics.types.first()?, translated)),
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => Some(Self::mk_ptr(ty, translated)),
            TyKind::FnPtr(_) => {
                let ptr_size = SizeExpr::Val(LayoutValue::mk_address_size());
                Some(Self {
                    size: SizeExprBound::ExactEq(ptr_size.clone()),
                    align: SizeExprBound::ExactEq(ptr_size.clone()),
                    offsets: OffsetGuarantees::None,
                })
            }
            TyKind::Array(elem_ty, elem_num) => Some(Self::mk_array(elem_ty, elem_num)),
            // For DSTs, we could think of a layout that is not only symbolic,
            // but also parametric in some meta data value.
            // For slice-like DSTs, we at least know that the alignment is the same as for the underlying array.
            //
            // See doc.rust-lang.org/reference/type-layout.html#r-layout.str
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Builtin(BuiltinTy::Str),
                ..
            }) => {
                Some(Self {
                    // Aligned to `u8`.
                    align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(ty, false))),
                    size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(ty, true))),
                    offsets: OffsetGuarantees::None,
                })
            }
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.slice
            TyKind::Slice(_) => Some(Self {
                align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(ty, false))),
                size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(ty, true))),
                offsets: OffsetGuarantees::None,
            }),
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.trait-object
            TyKind::DynTrait(_) => Some(Self {
                size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::DynSize)),
                align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::DynAlign)),
                offsets: OffsetGuarantees::None,
            }),
            // For the purpose of layout computation, the never type is (I think)
            // guaranteed to be a 1-ZST.
            TyKind::Never => Some(Self::one_zst()),
            _ => None,
        }
    }

    pub fn for_ty(ty: &Ty, translated: &TranslatedCrate) -> Option<Self> {
        Self::for_ty_inner(ty, translated, false)
    }
}

#[derive(Default)]
struct PartialLayoutGuarantees {
    size: Option<SizeExprBound>,
    align: Option<SizeExprBound>,
    offsets: IndexVec<VariantId, IndexVec<FieldId, SizeExprBound>>,
}

/// A structure that computes and stores originally symbolic layouts, which have been
/// normalized for a given target as much as possible. Will not be used during translation.
pub struct LayoutComputer<'a> {
    krate: &'a TranslatedCrate,
    target: Option<&'a TargetTriple>,
    cache: HashMap<Ty, LayoutGuarantees>,
    offset_cache: HashMap<Ty, IndexVec<VariantId, IndexVec<FieldId, SizeExprBound>>>,
    /// Stack to bail on cycles in the computation.
    stack: Vec<(Ty, PartialLayoutGuarantees)>,
}
impl<'a> LayoutComputer<'a> {
    pub fn new(krate: &'a TranslatedCrate, target: Option<&'a TargetTriple>) -> Self {
        Self {
            krate,
            target,
            cache: HashMap::new(),
            offset_cache: HashMap::new(),
            stack: Vec::new(),
        }
    }

    fn normalize_var(&mut self, var: &LayoutVar, parent_exact: bool) -> SizeExprBound {
        match var {
            LayoutVar::FieldOffset(variant_id, field_id) => {
                let (_, parts) = self.stack.last().unwrap();
                if let Some(fields) = parts.offsets.get(variant_id.unwrap_or(VariantId::ZERO))
                    && let Some(field_offset) = fields.get(*field_id)
                {
                    field_offset.clone().add_exact_info(parent_exact)
                } else {
                    SizeExprBound::make(SizeExpr::Var(var.clone()), parent_exact)
                }
            }
            LayoutVar::Size => {
                if let Some(size) = self.stack.last().and_then(|(_, part)| part.size.clone()) {
                    size.add_exact_info(parent_exact)
                } else {
                    SizeExprBound::make(SizeExpr::Var(LayoutVar::Size), parent_exact)
                }
            }
            LayoutVar::Align => {
                if let Some(align) = self.stack.last().and_then(|(_, part)| part.align.clone()) {
                    align.add_exact_info(parent_exact)
                } else {
                    SizeExprBound::make(SizeExpr::Var(LayoutVar::Align), parent_exact)
                }
            }
        }
    }

    fn normalize_val(&mut self, val: &LayoutValue, parent_exact: bool) -> SizeExprBound {
        match val {
            LayoutValue::SizeOf(ty) => {
                if ty == &Ty::mk_usize()
                    && let Some(target) = self.target
                    && let Some(target_specific_val) =
                        LayoutValue::mk_address_size_for(self.krate, target)
                {
                    SizeExprBound::make(SizeExpr::Val(target_specific_val), parent_exact)
                } else if let Some(layout) = self.compute_layout_guarantees(ty.clone()) {
                    layout.size.add_exact_info(parent_exact)
                } else {
                    SizeExprBound::make(
                        SizeExpr::Val(LayoutValue::SizeOf(ty.clone())),
                        parent_exact,
                    )
                }
            }
            LayoutValue::AlignOf(ty) => {
                if let Some(literal_ty) = ty.as_literal()
                    && let Some(target) = self.target
                    && let Some(target_specific_val) =
                        LayoutValue::make_primitive_align_for_target(literal_ty, self.krate, target)
                {
                    SizeExprBound::make(SizeExpr::Val(target_specific_val), parent_exact)
                } else if let Some(layout) = self.compute_layout_guarantees(ty.clone()) {
                    layout.align.add_exact_info(parent_exact)
                } else {
                    SizeExprBound::make(
                        SizeExpr::Val(LayoutValue::AlignOf(ty.clone())),
                        parent_exact,
                    )
                }
            }
            LayoutValue::Constant(c) => SizeExprBound::make(
                SizeExpr::Val(LayoutValue::Constant(c.clone())),
                parent_exact,
            ),
            LayoutValue::TargetDiscrSize => {
                if let Some(target) = self.target
                    && let Some(info) = self.krate.target_information.get(target)
                {
                    SizeExprBound::make(
                        SizeExpr::Val(LayoutValue::Constant(
                            ScalarValue::from_unchecked_uint(
                                UIntTy::U64,
                                info.c_enum_min_size as u128,
                            )
                            .to_constant(),
                        )),
                        parent_exact,
                    )
                } else {
                    SizeExprBound::make(SizeExpr::Val(LayoutValue::TargetDiscrSize), parent_exact)
                }
            }
            LayoutValue::TargetDiscrAlign => {
                if let Some(target) = self.target
                    && let Some(info) = self.krate.target_information.get(target)
                {
                    let target_discr_uint_ty = UIntTy::of_bit_width(info.c_enum_min_size).unwrap();
                    let target_discr_guarantees = self
                        .compute_layout_guarantees(Ty::new(TyKind::Literal(LiteralTy::UInt(
                            target_discr_uint_ty,
                        ))))
                        .unwrap();
                    target_discr_guarantees.align.add_exact_info(parent_exact)
                } else {
                    SizeExprBound::make(SizeExpr::Val(LayoutValue::TargetDiscrAlign), parent_exact)
                }
            }
            LayoutValue::DynSize | LayoutValue::DynAlign | LayoutValue::SliceLength => {
                SizeExprBound::make(SizeExpr::Val(val.clone()), parent_exact)
            }
        }
    }

    fn normalize_exact_size_expr(&mut self, size_expr: &mut SizeExprBound) {
        size_expr
            .update(|size_expr, parent_exact| self.normalize_size_expr(size_expr, parent_exact));
    }

    /// The return value denotes whether the result enforces a potentially new exactness value.
    /// The result is `Some` if anything can have changed about the input size expression.
    /// The content of the `Some` must be a conjunction of all recursive results.
    fn normalize_size_expr(&mut self, size_expr: &mut SizeExpr, exact_in: bool) -> bool {
        match size_expr {
            SizeExpr::Val(val) => {
                let ex = self.normalize_val(val, exact_in);
                let res = ex.is_exact_eq();
                *size_expr = ex.take();
                res
            }
            SizeExpr::Plus(summand1, summand2) => {
                let mut sum = Some(ScalarValue::mk_zero_usize());
                let exact1 = self.normalize_size_expr(summand1, exact_in);
                if let Some(inner_sum) = &sum
                    && let Some(c) = summand1.is_constant()
                    && let ConstantExprKind::Literal(Literal::Scalar(s)) = c.kind
                {
                    sum = *inner_sum + s;
                } else {
                    sum = None;
                }
                let exact2 = self.normalize_size_expr(summand2, exact1);
                if let Some(inner_sum) = &sum
                    && let Some(c) = summand2.is_constant()
                    && let ConstantExprKind::Literal(Literal::Scalar(s)) = c.kind
                {
                    sum = *inner_sum + s;
                } else {
                    sum = None;
                }
                if let Some(sum) = sum {
                    *size_expr = SizeExpr::Val(LayoutValue::Constant(sum.to_constant()));
                }
                exact2
            }
            SizeExpr::Scale(base, multiplier) => {
                let exact_out = self.normalize_size_expr(base, exact_in);
                if let Some(c) = base.is_constant()
                    && let ConstantExprKind::Literal(Literal::Scalar(base_scalar)) = c.kind
                    && let ConstantExprKind::Literal(Literal::Scalar(mult_scalar)) = multiplier.kind
                    && let Some(mult) = base_scalar * mult_scalar
                {
                    *size_expr = SizeExpr::Val(LayoutValue::Constant(mult.to_constant()));
                }
                exact_out
            }
            SizeExpr::AlignTo { base, target_align } => {
                let exact_1 = self.normalize_size_expr(base, exact_in);
                let exact_2 = self.normalize_size_expr(target_align, exact_1);
                if let Some(c1) = base.is_constant()
                    && let ConstantExprKind::Literal(Literal::Scalar(base_scalar)) = c1.kind
                    && let Some(c2) = target_align.is_constant()
                    && let ConstantExprKind::Literal(Literal::Scalar(target_scalar)) = c2.kind
                {
                    if base_scalar.is_multiple_of(&target_scalar) == Some(true) {
                        *size_expr = SizeExpr::Val(LayoutValue::Constant(c1));
                    } else if let Some(sum) = base_scalar + target_scalar
                        && let Some(rem) = base_scalar % target_scalar
                        && let Some(sub) = sum - rem
                    {
                        *size_expr = SizeExpr::Val(LayoutValue::Constant(sub.to_constant()));
                    }
                }
                exact_2
            }
            SizeExpr::Max(max_contenders) => {
                let mut max = Some(ScalarValue::mk_zero_usize());
                let mut curr_exact = exact_in;
                for contender in max_contenders.iter_mut() {
                    curr_exact = self.normalize_size_expr(contender, curr_exact);

                    if let Some(max) = &mut max
                        && let Some(c) = contender.is_constant()
                        && let ConstantExprKind::Literal(Literal::Scalar(scalar)) = c.kind
                    {
                        *max = (*max).max(scalar);
                    } else {
                        max = None;
                    }
                }
                if let Some(max) = max {
                    *size_expr = SizeExpr::Val(LayoutValue::Constant(max.to_constant()));
                }
                curr_exact
            }
            SizeExpr::Var(layout_var) => {
                let ex = self.normalize_var(layout_var, exact_in);
                let res = ex.is_exact_eq();
                *size_expr = ex.take();
                res
            }
            SizeExpr::Min(min_contender) => {
                let mut min = Some(ScalarValue::from_unchecked_uint(UIntTy::U128, u128::MAX));
                let mut curr_exact = exact_in;
                for contender in min_contender.iter_mut() {
                    curr_exact = self.normalize_size_expr(contender, curr_exact);

                    if let Some(min) = &mut min
                        && let Some(c) = contender.is_constant()
                        && let ConstantExprKind::Literal(Literal::Scalar(scalar)) = c.kind
                    {
                        *min = (*min).min(scalar);
                    } else {
                        min = None;
                    }
                }
                if let Some(min) = min {
                    *size_expr = SizeExpr::Val(LayoutValue::Constant(min.to_constant()));
                }
                curr_exact
            }
            SizeExpr::IfInhabited { .. } => todo!(),
        }
    }

    fn normalize_field_offset(&mut self, field_offset: &mut OffsetGuarantee, var_id: VariantId) {
        match field_offset {
            OffsetGuarantee::AtOffsetZero => {
                let (_, parts) = self.stack.last_mut().unwrap();
                let fields = parts.offsets.last_mut().unwrap();
                fields.push(SizeExprBound::ExactEq(SizeExpr::Val(
                    LayoutValue::Constant(ScalarValue::mk_zero_usize().to_constant()),
                )));
            }
            OffsetGuarantee::GuaranteedAlignment(size_expr) => {
                self.normalize_size_expr(size_expr, true);
            }
            OffsetGuarantee::ReprCField {
                predecessor,
                predecessor_size,
                own_ty,
            } => {
                let predecessor_end = if let Some(predecessor) = predecessor {
                    SizeExpr::Plus(
                        Box::new(SizeExpr::Var(LayoutVar::FieldOffset(
                            Some(var_id),
                            *predecessor,
                        ))),
                        Box::new(SizeExpr::Val(predecessor_size.clone())),
                    )
                } else {
                    SizeExpr::Val(predecessor_size.clone())
                };
                let mut offset_expr = SizeExpr::AlignTo {
                    base: Box::new(predecessor_end),
                    target_align: Box::new(SizeExpr::Val(LayoutValue::of_ty(own_ty, false))),
                };
                self.normalize_size_expr(&mut offset_expr, true);
                let (_, parts) = self.stack.last_mut().unwrap();
                let fields = parts.offsets.last_mut().unwrap();
                fields.push(SizeExprBound::ExactEq(offset_expr));
            }
        }
    }

    /// Computes the most precise layout guarantees we can deduce for this type.
    pub fn compute_layout_guarantees(&mut self, ty: Ty) -> Option<LayoutGuarantees> {
        if let Some(layout) = self.cache.get(&ty) {
            Some(layout.clone())
        } else if self.stack.iter().any(|(stack_ty, _)| &ty == stack_ty) {
            // In case of recursive/inductive layout constraints,
            // stop computation for that branch.
            None
        } else {
            let mut symbolic_layout = LayoutGuarantees::for_ty(&ty, self.krate)?;
            self.stack
                .push((ty.clone(), PartialLayoutGuarantees::default()));

            self.normalize_exact_size_expr(&mut symbolic_layout.align);
            let (_, parts) = self.stack.last_mut().unwrap();
            parts.align = Some(symbolic_layout.align.clone());

            if let Some(offsets) = self.offset_cache.get(&ty) {
                let (_, parts) = self.stack.last_mut().unwrap();
                parts.offsets = offsets.clone();
            } else {
                match &mut symbolic_layout.offsets {
                    OffsetGuarantees::Symbolic(ty) => {
                        if let Some(guarantees) = self.compute_layout_guarantees(ty.clone()) {
                            let (_, parts) = self.stack.last_mut().unwrap();
                            parts.offsets = self.offset_cache.get(ty).cloned().unwrap();
                            symbolic_layout.offsets = guarantees.offsets;
                        }
                    }
                    OffsetGuarantees::Variants(variants) => {
                        for (var_id, var) in variants.iter_mut_enumerated() {
                            let (_, parts) = self.stack.last_mut().unwrap();
                            debug_assert_eq!(parts.offsets.push(IndexVec::new()), var_id);
                            for field in var.iter_mut() {
                                self.normalize_field_offset(field, var_id);
                            }
                        }
                    }
                    OffsetGuarantees::Fields(fields) => {
                        let (_, parts) = self.stack.last_mut().unwrap();
                        debug_assert_eq!(parts.offsets.push(IndexVec::new()), VariantId::ZERO);
                        for field in fields {
                            self.normalize_field_offset(field, VariantId::ZERO);
                        }
                    }
                    OffsetGuarantees::None => (),
                }
            }

            self.normalize_exact_size_expr(&mut symbolic_layout.size);

            let (_, partial_guarantees) = self.stack.pop().unwrap();
            self.offset_cache
                .insert(ty.clone(), partial_guarantees.offsets);

            self.cache.insert(ty, symbolic_layout.clone());
            Some(symbolic_layout)
        }
    }

    pub fn lookup_pre_computed_offset(
        &self,
        ty: &Ty,
        variant_id: Option<VariantId>,
        field_id: FieldId,
    ) -> Option<&SizeExprBound> {
        self.offset_cache.get(ty).and_then(|variants| {
            variants
                .get(variant_id.unwrap_or(VariantId::ZERO))
                .and_then(|fields| fields.get(field_id))
        })
    }
}
