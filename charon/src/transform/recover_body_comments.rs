//! Take all the comments found in the original body and assign them to statements.

use std::collections::HashMap;

use derive_visitor::{visitor_enter_fn, visitor_enter_fn_mut, Drive, DriveMut};

use crate::llbc_ast::*;
use crate::transform::TransformCtx;

use super::ctx::LlbcPass;

pub struct Transform;
impl LlbcPass for Transform {
    // Constraints in the ideal case:
    // - each comment should be assigned to exactly one statement;
    // - the order of comments in the source should refine the partial order of control flow;
    // - a comment should come before the statement it was applied to.
    // We approximate this with a reasonable heuristic.
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        // Find for each line the statement span that starts the earliest as this is more likely to
        // correspond to what the comment was intended to point to.
        let mut best_span_for_line: HashMap<usize, Span> = Default::default();
        b.body.drive(&mut visitor_enter_fn(|st: &Statement| {
            let span = st.span;
            best_span_for_line
                .entry(span.span.beg.line)
                .and_modify(|best_span| {
                    // Find the span that starts the earliest, and among these the largest span.
                    if span.span.beg.col < best_span.span.beg.col
                        || (span.span.beg.col == best_span.span.beg.col
                            && span.span.end > best_span.span.end)
                    {
                        *best_span = span
                    }
                })
                .or_insert(span);
        }));

        // The map of lines to comments that apply to it.
        let mut comments_per_line: HashMap<usize, Vec<String>> = b
            .comments
            .iter()
            .cloned()
            .map(|(loc, comments)| (loc.line, comments))
            .collect();
        // Assign each comment to the first statement that has the best span for its starting line.
        // This may drop some comments if no statement starts with the relevant line (this can
        // happen if e.g. the statement was optimized out or the comment applied to an item
        // instead).
        b.body
            .drive_mut(&mut visitor_enter_fn_mut(|st: &mut Statement| {
                if best_span_for_line
                    .get(&st.span.span.beg.line)
                    .is_some_and(|best_span| *best_span == st.span)
                {
                    st.comments_before = comments_per_line
                        .remove(&st.span.span.beg.line)
                        .unwrap_or_default()
                }
            }));
    }
}
