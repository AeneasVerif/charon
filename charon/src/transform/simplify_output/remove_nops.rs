//! Remove the useless no-ops.
use crate::ast::*;
use crate::transform::TransformCtx;

use crate::transform::ctx::{LlbcPass, TransformPass, UllbcPass};

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut ullbc_ast::ExprBody) {
        for blk in &mut body.body {
            blk.statements
                .retain(|st| !(st.kind.is_nop() && st.comments_before.is_empty()))
        }
    }
}
impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut llbc_ast::ExprBody) {
        body.body.visit_blocks_bwd(|blk: &mut llbc_ast::Block| {
            blk.statements
                .retain(|st| !(st.kind.is_nop() && st.comments_before.is_empty()))
        });
    }
}

impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        ctx.for_each_fun_decl(|ctx, fun| match &mut fun.body {
            Body::Unstructured(body) => {
                <Self as UllbcPass>::transform_body(self, ctx, body);
            }
            Body::Structured(body) => {
                <Self as LlbcPass>::transform_body(self, ctx, body);
            }
            _ => {}
        });
    }
}
