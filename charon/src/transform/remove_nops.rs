//! Remove the useless no-ops.

use crate::llbc_ast::{ExprBody, RawStatement, Statement};
use crate::transform::TransformCtx;
use take_mut::take;

use super::ctx::LlbcPass;

fn transform_st(s: &mut Statement) {
    if let RawStatement::Sequence(seq) = &mut s.content {
        // Remove all the `Nop`s from this sequence.
        if seq.iter().any(|st| st.content.is_nop()) {
            seq.retain(|st| !st.content.is_nop())
        }
        // Replace an empty sequence with a `Nop`.
        if seq.is_empty() {
            take(&mut s.content, |_| RawStatement::Nop)
        }
    }
}

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        b.body.transform(&mut |st| {
            transform_st(st);
            None
        });
    }
}
