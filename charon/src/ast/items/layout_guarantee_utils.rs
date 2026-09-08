use std::collections::HashMap;

use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA, VariantName};
use serde_state::{DeserializeState, SerializeState};
use tracing::debug;

use crate::{
    ast::{
        AlignmentModifier, BuiltinTy, ConstantExpr, ConstantExprKind, ExactSizeExpr,
        ExactSizeExprKind, Field, FieldId, HashConsSerializerState, IndexVec, IntTy, Layout,
        LiteralTy, MetadataValue, OffsetGuarantee, ReprAlgorithm, ReprOptions, ScalarValue,
        SubstVisitor, TargetInfo, TargetTriple, TranslatedCrate, Ty, TyKind, TypeDeclKind,
        TypeDeclRef, UIntTy, VariantId, VariantLayout, VisitAstMut,
    },
    formatter::FmtCtx,
    pretty::FmtWithCtx,
};

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
        translated: Option<&TranslatedCrate>,
        target: Option<&TargetTriple>,
    ) -> Option<IndexVec<VariantId, IndexVec<FieldId, OffsetGuarantee>>> {
        match self {
            Self::Variants(variants_guarantees) => Some(variants_guarantees),
            Self::None if expected_variants.is_some() => Some(
                (0..expected_variants.unwrap())
                    .map(|_| vec![].into())
                    .collect(),
            ),
            Self::Symbolic(ty) => {
                let guarantees_for_ty = LayoutGuarantees::for_ty(&ty, translated?, target)?;
                if let OffsetGuarantees::Symbolic(ty2) = &guarantees_for_ty.offsets
                    && ty == *ty2
                {
                    // Break cycles.
                    None
                } else {
                    guarantees_for_ty
                        .offsets
                        .get_variants(expected_variants, translated, target)
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
                        .map(|offset| offset.guarantee.clone())
                        .collect()
                } else {
                    None
                };
            if let Some(fields) = fields {
                offsets.push(fields);
            } else {
                offsets.push(IndexVec::new());
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
    pub size: ExactSizeExpr,
    pub align: ExactSizeExpr,
    pub offsets: OffsetGuarantees,
}

struct LayoutGuaranteeComputer<'a, 'b> {
    krate: &'a TranslatedCrate,
    target: Option<&'b TargetTriple>,
}

fn expr_of_ty(ty: &Ty, is_size: bool) -> ExactSizeExprKind {
    if is_size {
        ExactSizeExprKind::Constant(ConstantExpr::new(
            ConstantExprKind::SizeOf(ty.clone()),
            Ty::mk_usize(),
        ))
    } else {
        ExactSizeExprKind::Constant(ConstantExpr::new(
            ConstantExprKind::AlignOf(ty.clone()),
            Ty::mk_usize(),
        ))
    }
}

fn mk_address_size() -> ExactSizeExprKind {
    ExactSizeExprKind::Constant(ConstantExpr::new(
        ConstantExprKind::SizeOf(Ty::mk_usize()),
        Ty::mk_usize(),
    ))
}

fn mk_address_align() -> ExactSizeExprKind {
    ExactSizeExprKind::Constant(ConstantExpr::new(
        ConstantExprKind::AlignOf(Ty::mk_usize()),
        Ty::mk_usize(),
    ))
}

impl<'a, 'b> LayoutGuaranteeComputer<'a, 'b> {
    pub(super) fn new(krate: &'a TranslatedCrate, target: Option<&'b TargetTriple>) -> Self {
        Self { krate, target }
    }

    /// The layout of a pointer to `pointee`. Uses the symbolic size of meta-data.
    ///
    /// Based on [https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer.unsized].
    fn mk_ptr(&self, pointee: &Ty) -> LayoutGuarantees {
        let meta = pointee.get_ptr_metadata(self.krate).into_type();
        // If we have no metadata, the pointer is exactly the address value.
        let exact = meta.is_unit();
        let ptr_size = mk_address_size().into_expr();
        let ptr_align =
            ConstantExpr::new(ConstantExprKind::AlignOf(Ty::mk_usize()), Ty::mk_usize());
        let align = ExactSizeExprKind::Max(vec![
            ExactSizeExprKind::Constant(ptr_align.clone()).into_expr(),
            expr_of_ty(&meta, false).into_expr(),
        ]);
        let size = ExactSizeExpr::make(
            ExactSizeExprKind::AlignTo {
                base: ExactSizeExprKind::Plus(ptr_size, expr_of_ty(&meta, true).into_expr())
                    .into_expr(),
                target_align: align.clone().into_expr(),
            }
            .into_expr(),
            exact,
        );
        LayoutGuarantees {
            size,
            align: ExactSizeExpr::make(align.into_expr(), exact),
            // We have guarantee about the offsets of the pointer parts, especially since
            // the parts have no field IDs.
            offsets: OffsetGuarantees::None,
        }
    }

    /// Generates the layout guarantees for a (tagged) union.
    /// NOTE: Assumes the type to be repr(C)!
    fn mk_tagged_union<V, F>(
        &self,
        variants: V,
        tag_ty: Option<Ty>,
        is_union: bool,
    ) -> LayoutGuarantees
    where
        V: Iterator<Item = F>,
        F: Iterator<Item = Ty>,
    {
        let mut max_size = ExactSizeExprKind::Max(Vec::new());
        let mut max_align = ExactSizeExprKind::Max(Vec::new());
        let mut offsets = IndexVec::new();

        for (id, mut fields) in variants.enumerate() {
            // Unions don't have an actual structure, but a single field, which needs to be
            // handled as if it has the same repr annotation as the whole union.
            let variant_guarantees = if is_union {
                let mut guarantees = self.for_ty_inner(&fields.next().unwrap(), true).unwrap();
                if let Some(first_field) = guarantees.offsets.first_field_mut() {
                    *first_field = OffsetGuarantee::AtOffsetZero;
                }
                guarantees
            } else {
                LayoutGuarantees::mk_ordered_sequence_repr_c(
                    fields,
                    Some(VariantId::from_raw(id)),
                    tag_ty.clone(),
                )
            };
            max_size.add_max(variant_guarantees.size.unalign());
            max_align.add_max(variant_guarantees.align);
            let field_offsets = match variant_guarantees.offsets {
                OffsetGuarantees::Variants(mut variants) => variants.pop().unwrap(),
                OffsetGuarantees::Fields(fields) => fields,
                _ => IndexVec::new(),
            };
            offsets.push(field_offsets);
        }

        let align = max_align.into_expr();

        let size = ExactSizeExprKind::AlignTo {
            base: max_size.into_expr(),
            target_align: align.clone(),
        }
        .into_expr();
        // Since we assume repr(C), the guarantees are exact.
        LayoutGuarantees {
            size,
            align: align,
            offsets: OffsetGuarantees::Variants(offsets),
        }
    }

    /// There must be at most one non-1-ZST field in the single variant.
    /// Based on https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.transparent
    fn mk_transparent_layout_guarantees(
        &self,
        fields: &IndexVec<FieldId, Field>,
    ) -> Option<LayoutGuarantees> {
        let mut non_one_zst_ty = None;
        let mut field_guarantees = IndexVec::new();
        for field in fields.iter() {
            let ty = &field.ty;
            let layout = self.for_ty(ty)?;
            if layout.is_one_zst() {
                if non_one_zst_ty.is_some() {
                    return None; // More than one non-1-ZST field!
                }
                non_one_zst_ty = Some(ty.clone());
                if let Some(align) = layout.align.as_exact() {
                    field_guarantees.push(OffsetGuarantee::GuaranteedAlignment(align));
                } else {
                    field_guarantees.push(OffsetGuarantee::GuaranteedAlignment(
                        expr_of_ty(ty, false).into_expr(),
                    ));
                }
            } else {
                field_guarantees.push(OffsetGuarantee::GuaranteedAlignment(
                    expr_of_ty(ty, false).into_expr(),
                ));
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

    pub(super) fn for_type_decl(
        &self,
        td_kind: &TypeDeclKind,
        repr: &ReprOptions,
    ) -> Option<LayoutGuarantees> {
        match td_kind {
            TypeDeclKind::Struct(fields) => {
                if repr.transparent {
                    return self.mk_transparent_layout_guarantees(fields);
                }

                let fields = fields.iter().map(|field| field.ty.clone());

                if repr.repr_algo == ReprAlgorithm::C {
                    let repr_c_guarantees =
                        LayoutGuarantees::mk_ordered_sequence_repr_c(fields, None, None);
                    return Some(repr_c_guarantees);
                }

                let mut base_guarantees =
                    LayoutGuarantees::mk_unordered_sequence(fields, None, Some(repr));
                // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.align-packed
                match repr.align_modif {
                    Some(AlignmentModifier::Align(forced_align)) => {
                        base_guarantees.align.with_kind_mut(|align_k| {
                            align_k.add_max(
                                ExactSizeExprKind::Constant(
                                    ScalarValue::from_unchecked_uint(
                                        UIntTy::Usize,
                                        forced_align as u128,
                                    )
                                    .to_constant(),
                                )
                                .into_expr(),
                            )
                        });
                    }
                    Some(AlignmentModifier::Pack(n)) => {
                        base_guarantees.align = ExactSizeExpr::new(ExactSizeExprKind::Min(vec![
                            ExactSizeExprKind::Constant(
                                ScalarValue::from_unchecked_uint(UIntTy::Usize, n as u128)
                                    .to_constant(),
                            )
                            .into_expr(),
                            base_guarantees.align,
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
                    self.mk_transparent_layout_guarantees(fields)
                } else {
                    // An explicit discriminant type implies that the enum has also C representation.
                    // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.primitive.adt
                    // Also, both cases imply that the discriminant type is guaranteed to be either the specified
                    // type, or the default discriminant type for a target.
                    if repr.guarantees_fixed_field_order() {
                        let field_less = variants.iter().all(|variant| variant.fields.is_empty());

                        let discr_ty = Ty::new(TyKind::Literal(
                            if let Some(discr_ty) = &repr.explicit_discr_type {
                                *discr_ty
                            } else {
                                LiteralTy::Int(
                                    self.krate.the_target_information().c_enum_smallest_repr_ty,
                                )
                            },
                        ));

                        if field_less {
                            // For field-less enums with a guaranteed discriminant type, the whole layout is exactly the type.
                            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.primitive.enum
                            Some(LayoutGuarantees::mk_symbolic(discr_ty))
                        } else {
                            // For enums with fields and #[repr(C)], the whole layout is a tagged union with the
                            // specified discriminant and a union of each variant as a #[repr(C)] struct.
                            // See https://doc.rust-lang.org/reference/type-layout.html#primitive-representation-of-enums-with-fields
                            // and https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.c.adt
                            let variants = variants
                                .iter()
                                .map(|variant| variant.fields.iter().map(|field| field.ty.clone()));
                            Some(self.mk_tagged_union(variants, Some(discr_ty), false))
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
                        let mut max_size = ExactSizeExprKind::Max(Vec::new());
                        let mut max_align = ExactSizeExprKind::Max(Vec::new());
                        let mut offsets = IndexVec::new();

                        for (id, variant) in variants.iter_enumerated() {
                            let fields = variant.fields.iter().map(|field| field.ty.clone());
                            let variant_guarantees =
                                LayoutGuarantees::mk_unordered_sequence(fields, Some(id), None);
                            max_size.add_max(variant_guarantees.size.unalign());
                            max_align.add_max(variant_guarantees.align);

                            let field_offsets = match variant_guarantees.offsets {
                                OffsetGuarantees::Variants(mut variants) => variants.pop().unwrap(),
                                OffsetGuarantees::Fields(fields) => fields,
                                _ => IndexVec::new(),
                            };
                            offsets.push(field_offsets);
                        }

                        let align = max_align.into_expr();
                        let size = ExactSizeExprKind::AtLeast(
                            ExactSizeExprKind::AlignTo {
                                base: max_size.into_expr(),
                                target_align: align.clone(),
                            }
                            .into_expr(),
                        )
                        .into_expr();
                        // Since we assume repr(C), the guarantees are exact.
                        Some(LayoutGuarantees {
                            size,
                            align: ExactSizeExprKind::AtLeast(align).into_expr(),
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
                Some(self.mk_tagged_union(variants, None, true))
            }
            TypeDeclKind::Alias(ty) => Some(LayoutGuarantees::mk_symbolic(ty.clone())),
            _ => None,
        }
    }

    fn for_ty_inner(&self, ty: &Ty, force_repr_c: bool) -> Option<LayoutGuarantees> {
        match ty.kind() {
            // True Adt's (i.e. structs and enums) should have layout guarantees stored in
            // the corresponding type declaration.
            TyKind::Adt(TypeDeclRef {
                id,
                generics,
                builtin: None,
            }) => {
                if let Some(td) = self.krate.type_decls.get(*id)
                    && let Some(target) = self.target
                {
                    let ctx = FmtCtx {
                        translated: Some(self.krate),
                        ..FmtCtx::default()
                    };
                    let poly_guarantees = LayoutGuarantees::from_layout(td.layout.get(target)?)?;
                    debug!(
                        "Substituting in layout for {} with {} and guarantees {}",
                        ty.with_ctx(&ctx),
                        generics.with_ctx(&ctx),
                        poly_guarantees.with_ctx(&ctx)
                    );
                    Some(
                        SubstVisitor::new_allow_metadata(generics, None, false)
                            .visit(poly_guarantees)
                            .unwrap(),
                    )
                } else {
                    Some(LayoutGuarantees::mk_symbolic(ty.clone()))
                }
            }
            TyKind::Adt(TypeDeclRef {
                id: _,
                generics,
                builtin: Some(BuiltinTy::Tuple),
            }) => {
                if force_repr_c {
                    Some(LayoutGuarantees::mk_ordered_sequence_repr_c(
                        generics.types.iter().cloned(),
                        None,
                        None,
                    ))
                } else {
                    Some(LayoutGuarantees::mk_unordered_sequence(
                        generics.types.iter().cloned(),
                        None,
                        None,
                    ))
                }
            }
            TyKind::TypeVar(_) => Some(LayoutGuarantees::mk_symbolic(ty.clone())),
            TyKind::Literal(literal_ty) => Some(LayoutGuarantees::mk_primitive(
                literal_ty,
                self.krate.the_target_information(),
            )),
            TyKind::Adt(TypeDeclRef {
                id: _,
                builtin: Some(BuiltinTy::Box),
                generics,
            }) => Some(self.mk_ptr(generics.types.first()?)),
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => Some(self.mk_ptr(ty)),
            TyKind::FnPtr(_) => {
                let ptr_size = mk_address_size().into_expr();
                Some(LayoutGuarantees {
                    size: ptr_size.clone(),
                    align: ptr_size.clone(),
                    offsets: OffsetGuarantees::None,
                })
            }
            TyKind::Array(elem_ty, elem_num) => Some(LayoutGuarantees::mk_array(elem_ty, elem_num)),
            // For DSTs, we could think of a layout that is not only symbolic,
            // but also parametric in some meta data value.
            // For slice-like DSTs, we at least know that the alignment is the same as for the underlying array.
            //
            // See doc.rust-lang.org/reference/type-layout.html#r-layout.str
            TyKind::Adt(TypeDeclRef {
                builtin: Some(BuiltinTy::Str),
                ..
            }) => {
                Some(LayoutGuarantees {
                    // Aligned to `u8`.
                    align: expr_of_ty(&Ty::new(TyKind::Literal(LiteralTy::UInt(UIntTy::U8))), true)
                        .into_expr(),
                    size: ExactSizeExprKind::FromMetadata(MetadataValue::SliceLength).into_expr(),
                    offsets: OffsetGuarantees::None,
                })
            }
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.slice
            TyKind::Slice(_) => Some(LayoutGuarantees {
                align: expr_of_ty(ty, false).into_expr(),
                size: expr_of_ty(ty, true).into_expr(),
                offsets: OffsetGuarantees::None,
            }),
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.trait-object
            TyKind::DynTrait(_) => Some(LayoutGuarantees {
                size: ExactSizeExprKind::FromMetadata(MetadataValue::DynSize).into_expr(),
                align: ExactSizeExprKind::FromMetadata(MetadataValue::DynAlign).into_expr(),
                offsets: OffsetGuarantees::None,
            }),
            // For the purpose of layout computation, the never type is (I think)
            // guaranteed to be a 1-ZST.
            TyKind::Never => Some(LayoutGuarantees::one_zst()),
            TyKind::TraitType(_, _, _) => Some(LayoutGuarantees::mk_symbolic(ty.clone())),
            _ => None,
        }
    }

    /// Constructs the layout guarantees for the given type.
    ///
    /// NOTE: Must only ever be called in a context with a single target!
    /// Will panic otherwise.
    pub(super) fn for_ty(&self, ty: &Ty) -> Option<LayoutGuarantees> {
        self.for_ty_inner(ty, false)
    }
}

impl LayoutGuarantees {
    pub(super) fn one_zst() -> Self {
        Self {
            size: ExactSizeExprKind::Constant(ScalarValue::mk_zero_usize().to_constant())
                .into_expr(),
            align: ExactSizeExprKind::Constant(ScalarValue::mk_one_usize().to_constant())
                .into_expr(),
            offsets: OffsetGuarantees::None,
        }
    }

    /// Based on [https://doc.rust-lang.org/reference/type-layout.html#r-layout.array].
    pub(super) fn mk_array(elem_ty: &Ty, elem_num: &ConstantExpr) -> Self {
        Self {
            size: ExactSizeExprKind::Scale(expr_of_ty(elem_ty, true).into_expr(), elem_num.clone())
                .into_expr(),
            align: expr_of_ty(elem_ty, false).into_expr(),
            offsets: OffsetGuarantees::None,
        }
    }

    /// This is consistent with [`rustc_middle::ty::Ty::primitive_size`].
    ///
    /// However, currently it ignores potential inconsistencies with regard to
    /// [https://doc.rust-lang.org/reference/type-layout.html#r-layout.primitive.size].
    pub(super) fn mk_primitive(primitive: &LiteralTy, target_info: &TargetInfo) -> Self {
        let size = match primitive {
            LiteralTy::Int(IntTy::Isize) | LiteralTy::UInt(UIntTy::Usize) => {
                return Self {
                    size: mk_address_size().into_expr(),
                    align: mk_address_align().into_expr(),
                    offsets: OffsetGuarantees::None,
                };
            }
            LiteralTy::Int(int_ty) => int_ty.target_size(0),
            LiteralTy::UInt(uint_ty) => uint_ty.target_size(0),
            LiteralTy::Float(float_ty) => float_ty.target_size(),
            LiteralTy::Bool => 1,
            LiteralTy::Char => 4,
        };
        let align = target_info.primitive_alignments.get(primitive).unwrap();
        Self {
            size: ExactSizeExprKind::Constant(
                ScalarValue::from_unchecked_uint(UIntTy::Usize, size as u128).to_constant(),
            )
            .into_expr(),
            align: ExactSizeExprKind::Constant(
                ScalarValue::from_uint(
                    target_info.target_pointer_size,
                    UIntTy::Usize,
                    *align as u128,
                )
                .unwrap()
                .to_constant(),
            )
            .into_expr(),
            offsets: OffsetGuarantees::None,
        }
    }

    pub(super) fn mk_symbolic(ty: Ty) -> Self {
        Self {
            size: expr_of_ty(&ty, true).into_expr(),
            align: expr_of_ty(&ty, false).into_expr(),
            offsets: OffsetGuarantees::Symbolic(ty),
        }
    }

    /// Computes the layout of a fixed, but unordered sequence of elements of the given types.
    /// This covers the Rust representation of both tuples and structs.
    ///
    /// The returned [`LayoutGuarantees::offsets`] ignore the variant id and store the field
    /// offsets at index 0.
    pub(super) fn mk_unordered_sequence<I>(
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
            Some(
                ExactSizeExprKind::Constant(
                    ScalarValue::from_unchecked_uint(UIntTy::Usize, *p as u128).to_constant(),
                )
                .into_expr(),
            )
        } else {
            None
        };
        for (id, ty) in fields.enumerate() {
            let end_of_field = ExactSizeExprKind::Plus(
                ExactSizeExprKind::FieldOffset(variant_id, FieldId::from_raw(id)).into_expr(),
                expr_of_ty(&ty, true).into_expr(),
            );
            size_max.push(end_of_field.into_expr());
            align_max.push(expr_of_ty(&ty, false).into_expr());
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.alignment.packed-fields
            // and https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.rust.layout, point 2.
            let field_offset_guarantee =
                OffsetGuarantee::GuaranteedAlignment(if let Some(packed) = &packed_align {
                    ExactSizeExprKind::Min(vec![packed.clone(), expr_of_ty(&ty, false).into_expr()])
                        .into_expr()
                } else {
                    expr_of_ty(&ty, false).into_expr()
                });
            field_offsets.push(field_offset_guarantee);
        }

        // An empty tuple is the unit type.
        // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.tuple.unit.
        if size_max.is_empty() && align_max.is_empty() {
            return Self::one_zst();
        }

        let align = ExactSizeExprKind::Max(align_max).into_expr();
        Self {
            // The size is the end of the last field, i.e. the max of field ends, aligned.
            // This implicitly follows from
            // https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.rust.layout.struct
            size: ExactSizeExprKind::AtLeast(
                ExactSizeExprKind::AlignTo {
                    base: ExactSizeExprKind::Max(size_max).into_expr(),
                    target_align: align.clone(),
                }
                .into_expr(),
            )
            .into_expr(),
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.rust.layout, point 2.
            align: ExactSizeExprKind::AtLeast(align).into_expr(),
            offsets: OffsetGuarantees::Fields(field_offsets),
        }
    }

    /// This computes the repr(C) layout guarantees for a struct/variant with the given fields
    /// and tag layout.
    ///
    /// The returned [`LayoutGuarantees::offsets`] ignore the variant id and store the field
    /// offsets at index 0.
    pub(super) fn mk_ordered_sequence_repr_c<I>(
        fields: I,
        variant_id: Option<VariantId>,
        tag_ty: Option<Ty>,
    ) -> Self
    where
        I: Iterator<Item = Ty>,
    {
        let tag_exists = tag_ty.is_some();
        let mut align_max = Vec::new();
        // If there are no fields, the size will be just the tag or 0.
        let mut size = if let Some(tag_ty) = &tag_ty {
            align_max.push(expr_of_ty(tag_ty, false).into_expr());
            expr_of_ty(tag_ty, true).into_expr()
        } else {
            ExactSizeExprKind::Constant(ScalarValue::mk_zero_usize().to_constant()).into_expr()
        };
        let mut field_offsets = IndexVec::new();

        let mut peekable_fields = fields.enumerate().peekable();
        while let Some((id, ty)) = peekable_fields.next() {
            if peekable_fields.peek().is_none() {
                // Only the last field is relevant for the size here.
                size = ExactSizeExprKind::Plus(
                    ExactSizeExprKind::FieldOffset(variant_id, FieldId::from_raw(id)).into_expr(),
                    expr_of_ty(&ty, true).into_expr(),
                )
                .into_expr()
            }
            let field_align = expr_of_ty(&ty, false).into_expr();
            align_max.push(field_align);
            if id == 0 {
                if tag_exists {
                    field_offsets.push(OffsetGuarantee::ReprCField { predecessor: None });
                } else {
                    field_offsets.push(OffsetGuarantee::AtOffsetZero);
                }
            } else {
                field_offsets.push(OffsetGuarantee::ReprCField {
                    predecessor: Some(FieldId::from_raw(id - 1)),
                });
            }
        }

        let align = ExactSizeExprKind::Max(align_max).into_expr();
        Self {
            size: ExactSizeExprKind::AlignTo {
                base: size,
                target_align: align.clone(),
            }
            .into_expr(),
            align: align,
            offsets: OffsetGuarantees::Fields(field_offsets),
        }
    }

    pub fn from_layout(layout: &Layout) -> Option<Self> {
        Some(Self {
            size: layout.size.guarantee.clone()?,
            align: layout.align.guarantee.clone()?,
            offsets: OffsetGuarantees::from_layout(&layout.variant_layouts),
        })
    }

    /// Constructs the layout guarantees for the type declaration.
    ///
    /// NOTE: Must only ever be called in a context with a single target!
    /// Will panic otherwise.
    #[tracing::instrument(skip(krate))]
    pub fn for_type_decl(
        td_kind: &TypeDeclKind,
        krate: &TranslatedCrate,
        repr: &ReprOptions,
    ) -> Option<LayoutGuarantees> {
        let comp = LayoutGuaranteeComputer::new(krate, None);
        comp.for_type_decl(td_kind, repr)
    }

    /// Constructs the layout guarantees for the given type.
    ///
    /// NOTE: Must only ever be called in a context with a single target!
    /// Will panic otherwise.
    pub fn for_ty(ty: &Ty, krate: &TranslatedCrate, target: Option<&TargetTriple>) -> Option<Self> {
        let comp = LayoutGuaranteeComputer::new(krate, target);
        comp.for_ty(ty)
    }

    fn is_one_zst(&self) -> bool {
        self.size
            == ExactSizeExprKind::Constant(ScalarValue::mk_zero_usize().to_constant()).into_expr()
            && self.align
                == ExactSizeExprKind::Constant(ScalarValue::mk_one_usize().to_constant())
                    .into_expr()
            && self.offsets == OffsetGuarantees::None
    }
}

#[derive(Default)]
struct PartialLayoutGuarantees {
    align: Option<ExactSizeExpr>,
    offsets: IndexVec<VariantId, IndexVec<FieldId, ExactSizeExpr>>,
}

/// A structure that computes and stores originally symbolic layouts, which have been
/// normalized for a given target as much as possible. Will not be used during translation.
pub struct LayoutComputer<'a> {
    krate: &'a TranslatedCrate,
    target: &'a TargetTriple,
    cache: HashMap<Ty, LayoutGuarantees>,
    offset_cache: HashMap<Ty, IndexVec<VariantId, IndexVec<FieldId, ExactSizeExpr>>>,
    /// Stack to bail on cycles in the computation.
    stack: Vec<(Ty, PartialLayoutGuarantees)>,
}

impl<'a> LayoutComputer<'a> {
    pub fn new(krate: &'a TranslatedCrate, target: &'a TargetTriple) -> Self {
        Self {
            krate,
            target,
            cache: HashMap::new(),
            offset_cache: HashMap::new(),
            stack: Vec::new(),
        }
    }

    // Wrapper function to enable normalization of symbolic field offsets.
    fn normalize_size(&self, ty: Ty, mut size_expr: ExactSizeExprKind) -> ExactSizeExpr {
        #[derive(Visitor)]
        struct OffsetVisitor<'a, 'b> {
            ty: Ty,
            comp: &'b LayoutComputer<'a>,
        }
        impl<'a, 'b> VisitAstMut for OffsetVisitor<'a, 'b> {
            fn visit_exact_size_expr_kind(
                &mut self,
                x: &mut ExactSizeExprKind,
            ) -> ::std::ops::ControlFlow<Self::Break> {
                if let ExactSizeExprKind::FieldOffset(var, f) = x
                    && let Some(offset) = self.comp.lookup_pre_computed_offset(&self.ty, *var, *f)
                    && let Some(offset) = offset.is_exact()
                {
                    *x = offset.kind().clone();
                }
                self.visit_inner(x)
            }
        }

        OffsetVisitor { ty, comp: self }.visit_exact_size_expr_kind(&mut size_expr);
        size_expr.into_expr().normalize(self.krate, self.target)
    }

    fn normalize_field_offset(
        &mut self,
        field_offset: &mut OffsetGuarantee,
        var_id: Option<VariantId>,
        own_id: FieldId,
        field_tys: impl Fn(FieldId) -> Ty,
        discr_size: &Option<ExactSizeExpr>,
    ) {
        match field_offset {
            OffsetGuarantee::AtOffsetZero => {
                let (_, parts) = self.stack.last_mut().unwrap();
                let fields = parts.offsets.last_mut().unwrap();
                fields.push(
                    ExactSizeExprKind::Constant(ScalarValue::mk_zero_usize().to_constant())
                        .into_expr(),
                );
            }
            OffsetGuarantee::GuaranteedAlignment(size_expr) => {
                *size_expr = size_expr.clone().normalize(self.krate, self.target);
            }
            OffsetGuarantee::ReprCField { predecessor } => {
                let (_, parts) = self.stack.last_mut().unwrap();
                let fields = parts.offsets.last_mut().unwrap();
                let predecessor_end = if let Some(pre) = predecessor {
                    let pre_ty = field_tys(*pre);
                    ExactSizeExprKind::Plus(
                        ExactSizeExprKind::FieldOffset(var_id, *pre).into_expr(),
                        ExactSizeExprKind::Constant(ConstantExpr::new(
                            ConstantExprKind::SizeOf(pre_ty),
                            Ty::mk_usize(),
                        ))
                        .into_expr(),
                    )
                    .into_expr()
                } else if let Some(discr_size) = discr_size {
                    discr_size.clone()
                } else {
                    ExactSizeExprKind::zero().into_expr()
                };
                let own_ty = field_tys(own_id);
                let mut offset_expr = ExactSizeExprKind::AlignTo {
                    base: predecessor_end,
                    target_align: expr_of_ty(&own_ty, false).into_expr(),
                }
                .into_expr();
                offset_expr = offset_expr.normalize(self.krate, self.target);
                fields.push(offset_expr);
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
            let mut symbolic_layout = LayoutGuarantees::for_ty(&ty, self.krate, Some(self.target))?;
            self.stack
                .push((ty.clone(), PartialLayoutGuarantees::default()));

            symbolic_layout.align = symbolic_layout
                .align
                .clone()
                .normalize(self.krate, self.target);
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
                        let ty_decl = self.krate.type_decls.get(ty.as_adt_id().unwrap()).unwrap();
                        let base_layout = ty_decl.layout.get(self.target).unwrap();
                        let discr_ty = if base_layout.is_c_repr() {
                            Some(
                                base_layout
                                    .repr
                                    .explicit_discr_type
                                    .unwrap_or(LiteralTy::Int(
                                        self.krate
                                            .target_information
                                            .get(self.target)
                                            .unwrap()
                                            .c_enum_smallest_repr_ty,
                                    )),
                            )
                        } else {
                            None
                        };
                        let discr_size = discr_ty
                            .and_then(|ty| {
                                self.compute_layout_guarantees(Ty::new(TyKind::Literal(ty)))
                            })
                            .map(|guarantees| guarantees.size);

                        for (var_id, var) in variants.iter_mut_enumerated() {
                            let (_, parts) = self.stack.last_mut().unwrap();
                            debug_assert_eq!(parts.offsets.push(IndexVec::new()), var_id);
                            let get_field_ty =
                                |f_id| ty_decl.get_field(Some(var_id), f_id).unwrap().ty.clone();
                            for (f_id, field) in var.iter_mut_enumerated() {
                                self.normalize_field_offset(
                                    field,
                                    Some(var_id),
                                    f_id,
                                    get_field_ty,
                                    &discr_size,
                                );
                            }
                        }
                    }
                    OffsetGuarantees::Fields(fields) => {
                        let ty_decl = self.krate.type_decls.get(ty.as_adt_id().unwrap()).unwrap();
                        let (_, parts) = self.stack.last_mut().unwrap();
                        debug_assert_eq!(parts.offsets.push(IndexVec::new()), VariantId::ZERO);
                        let get_field_ty = |f_id| ty_decl.get_field(None, f_id).unwrap().ty.clone();
                        for (f_id, field) in fields.iter_mut_enumerated() {
                            self.normalize_field_offset(field, None, f_id, get_field_ty, &None);
                        }
                    }
                    OffsetGuarantees::None => (),
                }
            }

            let (_, partial_guarantees) = self.stack.pop().unwrap();
            self.offset_cache
                .insert(ty.clone(), partial_guarantees.offsets);

            symbolic_layout.size =
                self.normalize_size(ty.clone(), symbolic_layout.size.kind().clone());

            self.cache.insert(ty, symbolic_layout.clone());
            Some(symbolic_layout)
        }
    }

    pub fn lookup_pre_computed_offset(
        &self,
        ty: &Ty,
        variant_id: Option<VariantId>,
        field_id: FieldId,
    ) -> Option<&ExactSizeExpr> {
        self.offset_cache.get(ty).and_then(|variants| {
            variants
                .get(variant_id.unwrap_or(VariantId::ZERO))
                .and_then(|fields| fields.get(field_id))
        })
    }
}
