use crate::llbc_ast::*;
use crate::transform::TransformCtx;

use crate::transform::ctx::TransformPass;

pub struct Transform;
impl TransformPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.erase_body_lifetimes
    }

    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        ctx.for_each_body(|_, body| {
            body.dyn_visit_mut(|r: &mut Region| {
                if r.is_body() {
                    *r = Region::Erased;
                }
            });
        });
    }
}
