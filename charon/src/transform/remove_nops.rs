//! Remove the useless no-ops.

use derive_visitor::{visitor_enter_fn_mut, DriveMut};

use crate::llbc_ast::*;
use crate::transform::TransformCtx;

use super::ctx::LlbcPass;

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, b: &mut ExprBody) {
        b.body
            .drive_mut(&mut visitor_enter_fn_mut(|blk: &mut Block| {
                // Remove all the `Nop`s from this sequence.
                if blk.statements.iter().any(|st| st.content.is_nop()) {
                    blk.statements.retain(|st| !st.content.is_nop())
                }
            }));
    }
}
