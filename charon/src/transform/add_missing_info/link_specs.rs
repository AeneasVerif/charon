use crate::ast::*;
use crate::transform::{TransformCtx, ctx::TransformPass};

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let mut attrs = Vec::new();
        for (spec_id, item) in ctx.translated.all_items_with_ids() {
            let ItemId::Fun(spec_id) = spec_id else {
                continue;
            };
            for attr in &item.item_meta().attr_info.attributes {
                match attr {
                    Attribute::IsPrecondition(parent_id) => {
                        attrs.push((*parent_id, Attribute::HasPrecondition(spec_id)));
                    }
                    Attribute::IsPostcondition(parent_id) => {
                        attrs.push((*parent_id, Attribute::HasPostcondition(spec_id)));
                    }
                    _ => {}
                }
            }
        }

        for (parent_id, attr) in attrs {
            let Some(mut parent) = ctx.translated.get_item_mut(parent_id) else {
                continue;
            };
            parent.item_meta().attr_info.attributes.push(attr);
        }
    }
}
