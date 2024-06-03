//! Remove the useless no-ops.

use crate::llbc_ast::{ExprBody, RawStatement, Statement};
use crate::meta::combine_span;
use crate::transform::TransformCtx;
use take_mut::take;

use super::ctx::LlbcPass;

fn transform_st(s: &mut Statement) {
    if let RawStatement::Sequence(s1, _) = &s.content {
        if s1.content.is_nop() {
            take(s, |s| {
                let (s1, s2) = s.content.to_sequence();
                Statement {
                    content: s2.content,
                    span: combine_span(&s1.span, &s2.span),
                }
            })
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
