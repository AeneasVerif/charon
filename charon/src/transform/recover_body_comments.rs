//! Take all the comments found in the original body and assign them to statements.

use derive_visitor::{visitor_enter_fn_mut, DriveMut};

use crate::llbc_ast::*;
use crate::transform::TransformCtx;

use super::ctx::LlbcPass;

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        // Constraints in the ideal case:
        // - each comment should be assigned to exactly one statement;
        // - the order of comments in the source should refine the partial order of control flow;
        // - a comment should come before the statement it was applied to.
        // Statement spans are way too imprecise for that.

        // This is a pretty terrible heuristic but the spans are really terrible.
        let mut comments: Vec<(usize, Vec<String>)> = b.comments.clone();
        b.body
            .drive_mut(&mut visitor_enter_fn_mut(|st: &mut Statement| {
                let st_line = st.span.span.beg.line;
                st.comments_before = comments
                    .extract_if(|(i, _)| *i <= st_line)
                    .flat_map(|(_, comments)| comments)
                    .collect();
            }));
    }
}
