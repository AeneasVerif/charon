//! Compute layout facts guaranteed by the language, following the rules of the Rust Reference:
//! <https://doc.rust-lang.org/reference/type-layout.html>.
use itertools::Itertools;

use crate::ast::*;
use crate::options::TranslateOptions;
use crate::transform::{TransformCtx, ctx::TransformPass};

pub struct Transform;

struct Guarantees {
    size: SizeExpr,
    align: SizeExpr,
    offsets: IndexVec<VariantId, IndexVec<FieldId, OffsetGuarantee>>,
}

fn compute_guarantees(
    krate: &TranslatedCrate,
    target: &TargetTriple,
    decl: &TypeDecl,
) -> Option<Guarantees> {
    let layout = decl.layout.get(target)?;
    let repr = &layout.repr;
    let field_tys = |fields: &IndexVec<FieldId, Field>| {
        fields.iter().map(|field| field.ty.clone()).collect_vec()
    };

    // The fields of each variant. Structs and unions are modeled as having exactly one variant.
    let variants: Vec<(Option<VariantId>, Vec<Ty>)> = match &decl.kind {
        TypeDeclKind::Struct(fields) | TypeDeclKind::Union(fields) => {
            vec![(None, field_tys(fields))]
        }
        TypeDeclKind::Enum(variants) => variants
            .iter_enumerated()
            .map(|(id, variant)| (Some(id), field_tys(&variant.fields)))
            .collect(),
        // An alias has the layout of the aliased type.
        TypeDeclKind::Alias(ty) => {
            return Some(Guarantees {
                size: SizeExpr::size_of(ty),
                align: SizeExpr::align_of(ty),
                offsets: IndexVec::new(),
            });
        }
        TypeDeclKind::Opaque | TypeDeclKind::Error(_) => return None,
    };

    // `repr(packed)` caps the alignment of each field, for the purpose of positioning them.
    // <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.alignment.packed-fields>
    let field_align = |ty: &Ty| {
        let align = SizeExpr::align_of(ty);
        match repr.align_modif {
            Some(AlignmentModifier::Pack(pack)) => {
                SizeExprKind::Min(vec![align, SizeExpr::from_usize(pack.into())]).into_expr()
            }
            _ => align,
        }
    };

    // The alignment of the type is the largest of the given alignments; `repr(align)` raises it.
    // <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.alignment.align>
    let type_align = |mut aligns: Vec<SizeExpr>| {
        if let Some(AlignmentModifier::Align(align)) = repr.align_modif {
            aligns.push(SizeExpr::from_usize(align.into()));
        }
        SizeExpr::max_align(aligns)
    };

    // The type has the layout of its single non-1-ZST field. Since the other fields are 1-ZSTs,
    // that's the maximum size and alignment over all the fields.
    // <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.transparent>
    if repr.transparent {
        let Ok([(_, fields)]) = <[_; 1]>::try_from(variants) else {
            unreachable!("repr(transparent) on a type with multiple variants");
        };
        let size = SizeExpr::max_size(fields.iter().map(SizeExpr::size_of).collect());
        let align = SizeExpr::max_align(fields.iter().map(SizeExpr::align_of).collect());
        let offsets = fields
            .iter()
            .map(SizeExpr::align_of)
            .map(OffsetGuarantee::GuaranteedAlignment)
            .collect();
        return Some(Guarantees {
            size,
            align,
            offsets: [offsets].into(),
        });
    }

    // `repr(C)` and `repr(int)` enums have a tag of the given type, or of the C default one.
    // <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.c.enum>
    // <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.primitive.enum>
    let tag_ty = (decl.kind.is_enum() && repr.guarantees_fixed_field_order()).then(|| {
        let int_ty = repr.explicit_discr_type.unwrap_or(IntegerTy::Signed(
            krate.target_information[target].c_enum_smallest_repr_ty,
        ));
        TyKind::Scalar(ScalarTy::Integer(int_ty)).into_ty()
    });
    let is_repr_c_like = repr.repr_algo == ReprAlgorithm::C || tag_ty.is_some();

    // All the fields are at offset zero; the size is the largest field size rounded up to the alignment.
    // <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.c.union>.
    if decl.kind.is_union() && is_repr_c_like {
        let Ok([(_, fields)]) = <[_; 1]>::try_from(variants) else {
            unreachable!("union with multiple variants");
        };
        let offsets = vec![OffsetGuarantee::AtOffset(SizeExpr::from_usize(0)); fields.len()].into();
        let align = type_align(fields.iter().map(field_align).collect());
        let size = SizeExpr::align_to(
            SizeExpr::max_size(fields.iter().map(SizeExpr::size_of).collect()),
            align.clone(),
        );
        return Some(Guarantees {
            size,
            align,
            offsets: [offsets].into(),
        });
    }

    // A field-less enum has the layout of its tag.
    // <https://doc.rust-lang.org/reference/type-layout.html#reprc-field-less-enums>
    // <https://doc.rust-lang.org/reference/type-layout.html#primitive-representation-of-field-less-enums>
    if let TypeDeclKind::Enum(variants) = &decl.kind
        && variants.iter().all(|variant| variant.fields.is_empty())
        && let Some(tag_ty) = &tag_ty
    {
        return Some(Guarantees {
            size: SizeExpr::size_of(tag_ty),
            align: SizeExpr::align_of(tag_ty),
            offsets: variants.map_ref(|_| IndexVec::new()),
        });
    }

    // The fields of each variant are laid out in order, each at the first properly aligned
    // offset after the previous one. The size is the end of the last field (of any variant),
    // rounded up to the alignment.
    // <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.c.struct>
    // <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.c.adt>
    // <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.primitive.adt>
    if is_repr_c_like {
        // The end of the last field of each variant.
        let variant_ends = variants.iter().filter_map(|(variant, fields)| {
            let (last, ty) = fields.iter().enumerate().next_back()?;
            let offset = SizeExpr::offset_of(decl.self_ref(), *variant, FieldId::from_usize(last));
            Some(SizeExprKind::Plus(offset, SizeExpr::size_of(ty)).into_expr())
        });
        let field_aligns = variants
            .iter()
            .flat_map(|(_, fields)| fields.iter().map(field_align))
            .collect_vec();
        let tag_size = tag_ty.as_ref().map(SizeExpr::size_of);
        let tag_align = tag_ty.as_ref().map(SizeExpr::align_of);

        let after_tag = tag_size.clone().map(|tag_size| match repr.repr_algo {
            // `repr(C)`: the fields of all variants form a union placed after the
            // tag `(tag, union { fields.. })`, so all first fields are at the offset of that union.
            ReprAlgorithm::C => OffsetGuarantee::AtOffset(SizeExpr::align_to(
                tag_size,
                SizeExpr::max_align(field_aligns.clone()),
            )),
            // `repr(int)`: each variant is its own struct `(tag, fields..)`, so
            // the first field is aligned to itself.
            ReprAlgorithm::Rust => OffsetGuarantee::ReprCField(FieldPredecessor::Tag),
        });

        let align = type_align(tag_align.into_iter().chain(field_aligns).collect());
        let size = SizeExpr::max_size(tag_size.into_iter().chain(variant_ends).collect());
        let size = SizeExpr::align_to(size, align.clone());
        let offsets = variants
            .iter()
            .map(|(_, fields)| {
                (0..fields.len())
                    .map(|f| match (f, &after_tag) {
                        (0, None) => OffsetGuarantee::AtOffset(SizeExpr::from_usize(0)),
                        (0, Some(after_tag)) => after_tag.clone(),
                        (f, _) => OffsetGuarantee::ReprCField(FieldPredecessor::Field(
                            FieldId::from_usize(f - 1),
                        )),
                    })
                    .collect()
            })
            .collect();
        return Some(Guarantees {
            size,
            align,
            offsets,
        });
    }

    // `repr(Rust)` only guarantees that the fields are aligned and don't overlap, and that the
    // alignment is at least that of the fields.
    // <https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.rust.layout>
    let fields = variants.iter().flat_map(|(_, fields)| fields);
    let align = type_align(fields.clone().map(field_align).collect());
    let size = SizeExpr::max_size(fields.map(SizeExpr::size_of).collect());
    let offsets = variants
        .iter()
        .map(|(_, fields)| {
            fields
                .iter()
                .map(|ty| OffsetGuarantee::GuaranteedAlignment(field_align(ty)))
                .collect()
        })
        .collect();
    Some(Guarantees {
        size: SizeExpr::at_least(SizeExpr::align_to(size, align.clone())),
        align: SizeExpr::at_least(align),
        offsets,
    })
}

impl TransformPass for Transform {
    fn should_run(&self, options: &TranslateOptions) -> bool {
        !options.no_compute_layout_guarantees
    }

    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let target = ctx
            .translated
            .target_information
            .keys()
            .exactly_one()
            .expect("layout guarantees expect exactly one target")
            .clone();

        ctx.for_each_type_decl(|ctx, decl| {
            let Some(guarantees) = compute_guarantees(&ctx.translated, &target, decl) else {
                return;
            };

            let Some(layout) = decl.layout.get_mut(&target) else {
                return;
            };

            // Normalize Inhabited predicates
            layout.inhabited = layout.inhabited.clone().normalize(&ctx.translated, None);
            for layout in layout.variant_layouts.iter_mut().flatten() {
                layout.inhabited = layout.inhabited.clone().normalize(&ctx.translated, None);
            }

            layout.size.guarantee = Some(guarantees.size.normalize(None, None, false));
            layout.align.guarantee = Some(guarantees.align.normalize(None, None, false));
            for (variant, offsets) in layout.variant_layouts.iter_mut().zip(guarantees.offsets) {
                if let Some(variant) = variant {
                    for (offset, guarantee) in variant.field_offsets.iter_mut().zip(offsets) {
                        offset.guarantee = Some(guarantee);
                    }
                }
            }
        });
    }
}
