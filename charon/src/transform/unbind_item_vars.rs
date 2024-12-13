//! Check that all supplied generic types match the corresponding generic parameters.

use derive_visitor::DriveMut;

use crate::ast::types_utils::SubstVisitor;

use super::{ctx::TransformPass, TransformCtx};

pub struct Check;
impl TransformPass for Check {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        for mut item in ctx.translated.all_items_mut() {
            let args = item.generic_params().free_identity_args();
            let mut visitor = SubstVisitor::new(&args);
            item.drive_mut(&mut visitor);
        }
        for decl in &ctx.translated.fun_decls {
            if let Ok(body_id) = decl.body {
                if let Some(body) = ctx.translated.bodies.get_mut(body_id) {
                    let args = decl.signature.generics.free_identity_args();
                    let mut visitor = SubstVisitor::new(&args);
                    body.drive_mut(&mut visitor);
                }
            }
        }
    }
}
