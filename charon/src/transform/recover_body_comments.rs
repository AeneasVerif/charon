//! Take all the comments found in the original body and assign them to statements.
use std::mem;

use crate::llbc_ast::*;
use crate::transform::TransformCtx;

use super::ctx::LlbcPass;

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, b: &mut ExprBody) {
        // Constraints in the ideal case:
        // - each comment should be assigned to exactly one statement;
        // - the order of comments in the source should refine the partial order of control flow;
        // - a comment should come before the statement it was applied to.

        // This is a pretty simple heuristic which is good enough for now.
        let mut comments: Vec<(usize, Vec<String>)> = b.comments.clone();
        b.body.visit_statements(|st: &mut Statement| {
            let st_line = st.span.span.beg.line;
            comments = mem::take(&mut comments)
                .into_iter()
                .filter_map(|(line, comments)| {
                    if line <= st_line {
                        st.comments_before.extend(comments);
                        None
                    } else {
                        Some((line, comments))
                    }
                })
                .collect();
        });
    }
}
