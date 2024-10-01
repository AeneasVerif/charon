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

        // This is a pretty simple heuristic which is good enough for now.
        let mut comments: Vec<(Loc, Vec<String>)> = b.comments.clone();
        b.body
            .drive_mut(&mut visitor_enter_fn_mut(|st: &mut Statement| {
                st.comments_before = comments
                    .extract_if(|(loc, _)| *loc == st.span.span.beg)
                    .flat_map(|(_, comments)| comments)
                    .collect();
            }));
    }
}
