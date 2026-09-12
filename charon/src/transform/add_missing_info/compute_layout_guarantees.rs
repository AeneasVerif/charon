//! Compute layout facts guaranteed by the language.
use itertools::Itertools;

use crate::ast::*;
use crate::options::TranslateOptions;
use crate::transform::{TransformCtx, ctx::TransformPass};

pub struct Transform;

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

        for decl in ctx.translated.type_decls.iter_mut() {
            let Some(layout) = decl.layout.get_mut(&target) else {
                continue;
            };
            let field_tys: Vec<_> = match &decl.kind {
                TypeDeclKind::Struct(fields) | TypeDeclKind::Union(fields)
                    if !layout.uninhabited =>
                {
                    fields.iter().map(|field| field.ty.clone()).collect()
                }
                TypeDeclKind::Enum(variants) if !layout.uninhabited => variants
                    .iter_enumerated()
                    .filter(|(id, _)| {
                        layout.variant_layouts[*id]
                            .as_ref()
                            .is_some_and(|vl| !vl.uninhabited)
                    })
                    .flat_map(|(_, variant)| variant.fields.iter())
                    .map(|field| field.ty.clone())
                    .collect(),
                _ => continue,
            };

            // `repr(packed)` caps the effective alignment of each field.
            let pack = match &layout.repr.align_modif {
                Some(AlignmentModifier::Pack(pack)) => Some(u128::from(*pack)),
                _ => None,
            };
            let field_aligns = field_tys.iter().cloned().map(|ty| {
                let align = SizeExprKind::Constant(ConstantExpr::new(
                    ConstantExprKind::AlignOf(ty),
                    Ty::mk_usize(),
                ))
                .into_expr();
                if let Some(pack) = pack {
                    SizeExprKind::Min(vec![align, SizeExprKind::from_usize(pack).into_expr()])
                        .into_expr()
                } else {
                    align
                }
            });
            let align = SizeExprKind::Max(field_aligns.collect()).into_expr();
            let align = align.normalize(None, None, false);

            let field_sizes = field_tys.into_iter().map(|ty| {
                SizeExprKind::Constant(ConstantExpr::new(
                    ConstantExprKind::SizeOf(ty),
                    Ty::mk_usize(),
                ))
                .into_expr()
            });
            let size = SizeExprKind::AlignTo {
                base: SizeExprKind::Max(field_sizes.collect()).into_expr(),
                target_align: align.clone(),
            }
            .into_expr();
            let size = size.normalize(None, None, false);

            layout.align.guarantee = Some(SizeExprKind::AtLeast(align).into_expr());
            layout.size.guarantee = Some(SizeExprKind::AtLeast(size).into_expr());
        }
    }
}
