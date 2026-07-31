use crate::ast::*;
use crate::transform::{TransformCtx, ctx::TransformPass};

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let mut specs = Vec::new();
        for (spec_id, item) in ctx.translated.all_items_with_ids() {
            let ItemId::Fun(spec_id) = spec_id else {
                continue;
            };
            for attr in &item.item_meta().attr_info.attributes {
                match attr {
                    Attribute::IsPrecondition(parent_id) => {
                        specs.push((spec_id, *parent_id, SpecKind::Precondition));
                    }
                    Attribute::IsPostcondition(parent_id) => {
                        specs.push((spec_id, *parent_id, SpecKind::Postcondition));
                    }
                    _ => {}
                }
            }
        }

        for (spec_id, parent_id, kind) in specs {
            if ctx.translated.get_item(parent_id).is_none() {
                continue;
            }
            let Some(ItemRefMut::Fun(spec)) = ctx.translated.get_item_mut(spec_id.into()) else {
                continue;
            };
            spec.src = ItemSource::Spec {
                kind,
                item: parent_id,
            };

            let mut parent = ctx.translated.get_item_mut(parent_id).unwrap();
            let attr = match kind {
                SpecKind::Precondition => Attribute::HasPrecondition(spec_id),
                SpecKind::Postcondition => Attribute::HasPostcondition(spec_id),
            };
            parent.item_meta().attr_info.attributes.push(attr);
        }
    }
}
