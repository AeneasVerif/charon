use crate::ast::*;
use crate::transform::{TransformCtx, ctx::TransformPass};

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let mut attrs = Vec::new();
        for (spec_id, fdecl) in ctx.translated.fun_decls.iter_mut_enumerated() {
            for attr in &fdecl.item_meta.attr_info.attributes {
                if let Attribute::IsContract { kind, target } = attr {
                    attrs.push((
                        *target,
                        Attribute::HasContract {
                            kind: kind.clone(),
                            contract: spec_id,
                        },
                    ));
                }
            }
        }

        for (target_id, attr) in attrs {
            match target_id {
                MaybeAssocItemId::Free(item_id) => {
                    let Some(mut item) = ctx.translated.get_item_mut(item_id) else {
                        continue;
                    };
                    item.item_meta().attr_info.attributes.push(attr);
                }
                MaybeAssocItemId::Assoc(trait_id, item_id) => {
                    let Some(trait_decl) = ctx.translated.trait_decls.get_mut(trait_id) else {
                        continue;
                    };
                    let attr_info = match item_id {
                        AssocItemId::Type(id) => &mut trait_decl.types[id].skip_binder.attr_info,
                        AssocItemId::Method(id) => {
                            &mut trait_decl.methods[id].skip_binder.item_meta.attr_info
                        }
                        AssocItemId::Const(id) => &mut trait_decl.consts[id].attr_info,
                    };
                    attr_info.attributes.push(attr);
                }
            }
        }
    }
}
