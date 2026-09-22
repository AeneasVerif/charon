//! Check that the layout guarantees computed by charon hold for the layouts chosen by rustc, using `-Zrandomize-layout`.

use charon_lib::ast::*;

mod util;
use macros::EnumIsA;
use util::*;

/// Number of different layout seeds to try.
const SEEDS: u64 = 10;

/// Values assumed for the pointer metadata of unsized types.
const DYN_SIZE: u128 = 12;
const DYN_ALIGN: u128 = 4;
const SLICE_LENGTH: u128 = 3;

#[derive(Debug, Copy, Clone, EnumIsA)]
enum BoundOp {
    Equal,
    AtLeast,
}

impl BoundOp {
    fn meet(self, other: BoundOp) -> BoundOp {
        match (self, other) {
            (BoundOp::Equal, BoundOp::Equal) => BoundOp::Equal,
            (BoundOp::AtLeast, _) | (_, BoundOp::AtLeast) => BoundOp::AtLeast,
        }
    }
}

/// A lower bound on a size, which is exact unless the expression contained an `at_least`.
#[derive(Debug, Copy, Clone)]
struct Bound {
    value: u128,
    op: BoundOp,
}

impl Bound {
    fn exact(value: u128) -> Self {
        Bound {
            value,
            op: BoundOp::Equal,
        }
    }

    fn at_least(value: u128) -> Self {
        Bound {
            value,
            op: BoundOp::AtLeast,
        }
    }

    fn check(&self, other: u128, msg: &str) {
        assert!(
            match self.op {
                BoundOp::Equal => other == self.value,
                BoundOp::AtLeast => other >= self.value,
            },
            "{msg}: bound {self:?} is not satisfied by {other}"
        );
    }
}

/// Evaluates size expressions against the layouts chosen by rustc (the ground truth).
struct Evaluator<'a> {
    krate: &'a TranslatedCrate,
    target: &'a TargetTriple,
}

impl Evaluator<'_> {
    fn target_info(&self) -> &TargetInfo {
        &self.krate.target_information[self.target]
    }

    fn layout_of(&self, id: TypeDeclId) -> Option<&Layout> {
        self.krate.type_decls.get(id)?.layout.get(self.target)
    }

    /// The size and alignment of `ty` chosen by rustc; `None` if not known (e.g. for the
    /// instantiation of a polymorphic type).
    fn size_align_of(&self, ty: &Ty) -> Option<(u128, u128)> {
        let ptr_size = self.target_info().target_pointer_size;
        Some(match ty.kind() {
            TyKind::Scalar(scalar) => (
                scalar.target_size(ptr_size) as u128,
                u128::from(*self.target_info().primitive_alignments.get(scalar)?),
            ),
            TyKind::Never => (0, 1),
            TyKind::Ref(_, pointee, _) | TyKind::RawPtr(pointee, _) => {
                let width = match pointee.get_ptr_metadata(self.krate) {
                    PtrMetadata::None => 1,
                    PtrMetadata::Length | PtrMetadata::VTable(_) => 2,
                    PtrMetadata::InheritFrom(_) => return None,
                };
                (width * u128::from(ptr_size), u128::from(ptr_size))
            }
            TyKind::Array(elem, len, _) => {
                let (size, align) = self.size_align_of(elem)?;
                (size * len.as_usize_literal()?, align)
            }
            TyKind::Slice(elem, _) => {
                let (size, align) = self.size_align_of(elem)?;
                (size * SLICE_LENGTH, align)
            }
            TyKind::DynTrait(_) => (DYN_SIZE, DYN_ALIGN),
            TyKind::Adt(ty_ref) => {
                let layout = self.layout_of(ty_ref.id)?;
                (
                    self.eval_exact(layout.size.chosen.as_ref()?)?,
                    self.eval_exact(layout.align.chosen.as_ref()?)?,
                )
            }
            _ => return None,
        })
    }

    /// The alignment of a field of type `ty` in a type with the given layout, as capped by `packed`.
    fn field_align(&self, layout: &Layout, ty: &Ty) -> Option<u128> {
        let (_, align) = self.size_align_of(ty)?;
        Some(match layout.repr.align_modif {
            Some(AlignmentModifier::Pack(pack)) => align.min(u128::from(pack)),
            _ => align,
        })
    }

    /// The offset of the given field chosen by rustc. For an unsized field, rustc records the
    /// offset before alignment; the actual offset is computed at runtime by aligning it.
    fn chosen_offset(&self, decl: &TypeDecl, variant: VariantId, field: FieldId) -> Option<u128> {
        let layout = decl.layout.get(self.target)?;
        let offset = layout.variant_layouts.get(variant)?.as_ref()?.field_offsets[field].chosen?;
        let ty = &decl.get_field(Some(variant), field)?.ty;
        let align = match ty.get_ptr_metadata(self.krate) {
            PtrMetadata::None => 1,
            _ => self.field_align(layout, ty)?,
        };
        Some(u128::from(offset).next_multiple_of(align))
    }

    fn eval_exact(&self, expr: &SizeExpr) -> Option<u128> {
        let bound = self.eval(expr)?;
        assert!(bound.op.is_equal(), "non-exact chosen size: {expr:?}");
        Some(bound.value)
    }

    /// Fold the evaluations of `values` with `f`; the result is exact iff all of them are.
    fn fold<'b>(
        &self,
        values: impl IntoIterator<Item = &'b SizeExpr>,
        f: impl Fn(u128, u128) -> u128,
    ) -> Option<Bound> {
        values
            .into_iter()
            .map(|value| self.eval(value))
            .reduce(|left, right| {
                let (left, right) = (left?, right?);
                Some(Bound {
                    value: f(left.value, right.value),
                    op: left.op.meet(right.op),
                })
            })?
    }

    /// Evaluate `expr`; `None` if it depends on a value we don't know.
    fn eval(&self, expr: &SizeExpr) -> Option<Bound> {
        Some(match expr.kind() {
            SizeExprKind::Constant(constant) => Bound::exact(match constant.kind() {
                ConstantExprKind::SizeOf(ty) => self.size_align_of(ty)?.0,
                ConstantExprKind::AlignOf(ty) => self.size_align_of(ty)?.1,
                ConstantExprKind::OffsetOf(ty_ref, variant, field) => {
                    let decl = self.krate.type_decls.get(ty_ref.id)?;
                    self.chosen_offset(decl, variant.unwrap_or(VariantId::from_usize(0)), *field)?
                }
                _ => constant.as_usize_literal()?,
            }),
            SizeExprKind::FromMetadata(metadata) => Bound::exact(match metadata {
                MetadataValue::DynSize => DYN_SIZE,
                MetadataValue::DynAlign => DYN_ALIGN,
                MetadataValue::SliceLength => SLICE_LENGTH,
            }),
            SizeExprKind::Max(values) => self.fold(values, u128::max)?,
            SizeExprKind::Min(values) => self.fold(values, u128::min)?,
            SizeExprKind::Plus(left, right) => self.fold([left, right], u128::strict_add)?,
            SizeExprKind::Scale(base, multiplier) => {
                let base = self.eval(base)?;
                Bound {
                    value: base.value * multiplier.as_usize_literal()?,
                    op: base.op,
                }
            }
            SizeExprKind::AtLeast(inner) => Bound::at_least(self.eval(inner)?.value),
            SizeExprKind::AlignTo { base, target_align } => {
                self.fold([base, target_align], u128::next_multiple_of)?
            }
            SizeExprKind::IfInhabited {
                ty,
                then_size,
                else_size,
            } => {
                let inhabited = ty
                    .inhabited_predicate(self.krate, Some(self.target))
                    .normalize(self.krate, Some(self.target))
                    .as_bool()?;
                self.eval(if inhabited { then_size } else { else_size })?
            }
        })
    }

    /// Check that the chosen value satisfies the guarantee. Returns `None` if the guarantee could
    /// not be evaluated.
    fn check_size(&self, size: &Size, msg: &str) -> Option<()> {
        let chosen = self.eval_exact(size.chosen.as_ref()?)?;
        let guarantee = self.eval(size.guarantee.as_ref()?)?;
        guarantee.check(chosen, msg);
        Some(())
    }

    /// Check that the chosen offset of the given field satisfies its guarantee. Returns `None` if
    /// the guarantee could not be evaluated.
    fn check_offset(
        &self,
        decl: &TypeDecl,
        variant_id: VariantId,
        field_id: FieldId,
        msg: &str,
    ) -> Option<()> {
        let layout = decl.layout.get(self.target)?;
        let variant = layout.variant_layouts[variant_id].as_ref()?;
        let fields = decl.get_fields(Some(variant_id))?;
        let chosen = self.chosen_offset(decl, variant_id, field_id)?;
        match variant.field_offsets[field_id].guarantee.as_ref()? {
            OffsetGuarantee::AtOffset(expr) => {
                assert_eq!(chosen, self.eval_exact(expr)?, "{msg}");
            }
            OffsetGuarantee::GuaranteedAlignment(expr) => {
                let align = self.eval(expr)?.value;
                assert!(
                    chosen.is_multiple_of(align),
                    "{msg}: offset {chosen} is not aligned to {align}"
                );
            }
            OffsetGuarantee::ReprCField(predecessor) => {
                let ptr_size = self.target_info().target_pointer_size;
                let predecessor_end = match predecessor {
                    FieldPredecessor::Tag => {
                        let tag_ty = layout.repr.explicit_discr_type.unwrap_or(IntegerTy::Signed(
                            self.target_info().c_enum_smallest_repr_ty,
                        ));
                        tag_ty.target_size(ptr_size) as u128
                    }
                    FieldPredecessor::Field(prev) => {
                        self.chosen_offset(decl, variant_id, *prev)?
                            + self.size_align_of(&fields[*prev].ty)?.0
                    }
                };
                let align = self.field_align(layout, &fields[field_id].ty)?;
                assert_eq!(chosen, predecessor_end.next_multiple_of(align), "{msg}");
            }
        }
        Some(())
    }
}

#[test]
fn fuzz_layout() -> anyhow::Result<()> {
    let source = std::fs::read_to_string("tests/ui/layout_examples.rs")?;
    let (mut checked, mut skipped) = (0, 0);
    for seed in 0..SEEDS {
        let krate = translate_rust_text(format!(
            "//@ rustc-args=-Zrandomize-layout -Zlayout-seed={seed}\n{source}"
        ))?;
        let target = krate.target_information.keys().next().unwrap();
        let eval = Evaluator {
            krate: &krate,
            target,
        };
        let mut count = |result: Option<()>| match result {
            Some(()) => checked += 1,
            None => skipped += 1,
        };

        for decl in krate.type_decls.iter() {
            let Some(layout) = decl.layout.get(target) else {
                continue;
            };
            let name = decl.item_meta.name.debug_repr(&krate);
            let msg = format!("seed {seed}, type {name}");
            count(eval.check_size(&layout.size, &format!("{msg}: size")));
            count(eval.check_size(&layout.align, &format!("{msg}: align")));
            for variant_id in layout.variant_layouts.indices() {
                let Some(fields) = decl.get_fields(Some(variant_id)) else {
                    continue;
                };
                for field_id in fields.indices() {
                    let msg = format!("{msg}: offset of {variant_id}.{field_id}");
                    count(eval.check_offset(decl, variant_id, field_id, &msg));
                }
            }
        }
    }
    eprintln!("checked {checked} guarantees, skipped {skipped}");
    assert!(checked > 0);
    Ok(())
}
