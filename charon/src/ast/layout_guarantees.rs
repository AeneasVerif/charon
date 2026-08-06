use std::collections::HashMap;

use derive_generic_visitor::*;
use serde_state::{DeserializeState, SerializeState};

use crate::{
    ast::{
        AlignmentModifier, BuiltinTy, ConstantExpr, ConstantExprKind, Field, FieldId,
        HashConsSerializerState, IntTy, Layout, LayoutValue, LayoutVar, Literal, LiteralTy,
        OffsetGuarantee, OffsetGuarantees, ReprAlgorithm, ReprOptions, ScalarValue, SizeExpr,
        SizeExprBound, TargetInfo, TargetTriple, TranslatedCrate, Ty, TyKind, TyVisitable,
        TypeDeclKind, TypeDeclRef, TypeId, UIntTy, VariantId,
    },
    ids::IndexVec,
};

#[derive(
    Debug, Clone, PartialEq, Eq, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
#[serde_state(state_implements = HashConsSerializerState)]
pub struct LayoutGuarantees {
    pub size: SizeExprBound,
    pub align: SizeExprBound,
    pub offsets: OffsetGuarantees,
}

struct LayoutGuaranteeComputer<'a, 'b> {
    krate: &'a TranslatedCrate,
    target: Option<&'b TargetTriple>,
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
        let ptr_size = LayoutValue::mk_address_size();
        let ptr_align = LayoutValue::mk_address_align();
        let align = SizeExpr::Max(vec![
            SizeExpr::Val(ptr_align.clone()),
            SizeExpr::Val(LayoutValue::of_ty(&meta, false)),
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
        LayoutGuarantees {
            size,
            align: SizeExprBound::make(align, exact),
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
        let mut max_size = SizeExpr::Max(Vec::new());
        let mut max_align = SizeExpr::Max(Vec::new());
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
        &self,
        fields: &IndexVec<FieldId, Field>,
    ) -> Option<LayoutGuarantees> {
        let mut non_one_zst_ty = None;
        let mut field_guarantees = IndexVec::new();
        for field in fields.iter() {
            let ty = &field.ty;
            let layout = self.for_ty(ty)?;
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
                        base_guarantees.align.map_mut(|align| {
                            align.max(SizeExpr::Val(LayoutValue::Constant(
                                ScalarValue::from_unchecked_uint(
                                    UIntTy::Usize,
                                    forced_align as u128,
                                )
                                .to_constant(),
                            )))
                        });
                    }
                    Some(AlignmentModifier::Pack(n)) => {
                        base_guarantees.align = SizeExprBound::ExactEq(SizeExpr::Min(vec![
                            SizeExpr::Val(LayoutValue::Constant(
                                ScalarValue::from_unchecked_uint(UIntTy::Usize, n as u128)
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
                    self.mk_transparent_layout_guarantees(fields)
                } else {
                    // An explicit discriminant type implies that the enum has also C representation.
                    // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.primitive.adt
                    // Also, both cases imply that the discriminant type is guaranteed to be either the specified
                    // type, or the default discriminant type for a target.
                    if repr.guarantees_fixed_field_order() {
                        let field_less = variants.iter().all(|variant| variant.fields.is_empty());

                        let discr_ty = if let Some(discr_ty) = &repr.explicit_discr_type {
                            discr_ty.clone()
                        } else {
                            Ty::new(TyKind::Literal(LiteralTy::Int(
                                self.krate.the_target_information().c_enum_repr_ty,
                            )))
                        };

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
                id: TypeId::Adt(type_decl_id),
                generics,
            }) => {
                if let Some(td) = self.krate.type_decls.get(*type_decl_id)
                    && let Some(target) = self.target
                {
                    let poly_guarantees = LayoutGuarantees::from_layout(td.layout.get(target)?);
                    Some(poly_guarantees.substitute(generics))
                } else {
                    Some(LayoutGuarantees::mk_symbolic(ty.clone()))
                }
            }
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Tuple,
                generics,
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
                id: TypeId::Builtin(BuiltinTy::Box),
                generics,
            }) => Some(self.mk_ptr(generics.types.first()?)),
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => Some(self.mk_ptr(ty)),
            TyKind::FnPtr(_) => {
                let ptr_size = SizeExpr::Val(LayoutValue::mk_address_size());
                Some(LayoutGuarantees {
                    size: SizeExprBound::ExactEq(ptr_size.clone()),
                    align: SizeExprBound::ExactEq(ptr_size.clone()),
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
                id: TypeId::Builtin(BuiltinTy::Str),
                ..
            }) => {
                Some(LayoutGuarantees {
                    // Aligned to `u8`.
                    align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(ty, false))),
                    size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(ty, true))),
                    offsets: OffsetGuarantees::None,
                })
            }
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.slice
            TyKind::Slice(_) => Some(LayoutGuarantees {
                align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(ty, false))),
                size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(ty, true))),
                offsets: OffsetGuarantees::None,
            }),
            // See https://doc.rust-lang.org/reference/type-layout.html#r-layout.trait-object
            TyKind::DynTrait(_) => Some(LayoutGuarantees {
                size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::DynSize)),
                align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::DynAlign)),
                offsets: OffsetGuarantees::None,
            }),
            // For the purpose of layout computation, the never type is (I think)
            // guaranteed to be a 1-ZST.
            TyKind::Never => Some(LayoutGuarantees::one_zst()),
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
            size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::Constant(
                ScalarValue::mk_zero_usize().to_constant(),
            ))),
            align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::Constant(
                ScalarValue::mk_one_usize().to_constant(),
            ))),
            offsets: OffsetGuarantees::None,
        }
    }

    /// Based on [https://doc.rust-lang.org/reference/type-layout.html#r-layout.array].
    pub(super) fn mk_array(elem_ty: &Ty, elem_num: &ConstantExpr) -> Self {
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
    pub(super) fn mk_primitive(primitive: &LiteralTy, target_info: &TargetInfo) -> Self {
        let size = match primitive {
            LiteralTy::Int(IntTy::Isize) | LiteralTy::UInt(UIntTy::Usize) => {
                return Self {
                    size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::mk_address_size())),
                    align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::mk_address_align())),
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
            size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::Constant(
                ScalarValue::from_unchecked_uint(UIntTy::Usize, size as u128).to_constant(),
            ))),
            align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::Constant(
                ScalarValue::mk_usize(target_info.target_pointer_size, *align).to_constant(),
            ))),
            offsets: OffsetGuarantees::None,
        }
    }

    pub(super) fn mk_symbolic(ty: Ty) -> Self {
        Self {
            size: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(&ty, true))),
            align: SizeExprBound::ExactEq(SizeExpr::Val(LayoutValue::of_ty(&ty, false))),
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
            Some(SizeExpr::Val(LayoutValue::Constant(
                ScalarValue::from_unchecked_uint(UIntTy::Usize, *p as u128).to_constant(),
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
        let mut last_ty = None;
        // If there are no fields, the size will be just the tag or 0.
        let mut size = if let Some(tag_ty) = &tag_ty {
            last_ty = Some(tag_ty.clone());
            align_max.push(SizeExpr::Val(LayoutValue::AlignOf(tag_ty.clone())));
            SizeExpr::Val(LayoutValue::SizeOf(tag_ty.clone()))
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
                        predecessor_size: LayoutValue::of_ty(&last_ty.unwrap(), true),
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

    pub fn from_layout(layout: &Layout) -> Self {
        Self {
            size: layout.size.guarantees.clone(),
            align: layout.align.guarantees.clone(),
            offsets: OffsetGuarantees::from_layout(&layout.variant_layouts),
        }
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
            let mut symbolic_layout = LayoutGuarantees::for_ty(&ty, self.krate, self.target)?;
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
