//! The MIR code often contains variables with type `Never`, and we want to get
//! rid of those. We proceed in two steps. First, we remove the instructions
//! `drop(v)` where `v` has type `Never` (it can happen - this module does the
//! filtering). Then, we filter the unused variables ([crate::remove_unused_locals]).
use crate::llbc_ast::*;
use crate::transform::TransformCtx;

use super::ctx::LlbcPass;

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, b: &mut ExprBody) {
        let locals = &b.locals;
        b.body.visit_statements(|st: &mut Statement| {
            // Filter the statement by replacing it with `Nop` if it is a `Drop(x)` where
            // `x` has type `Never`. Otherwise leave it unchanged.
            if let RawStatement::Drop(p) = &st.content
                && p.as_local()
                    .is_some_and(|var_id| locals[var_id].ty.kind().is_never())
            {
                st.content = RawStatement::Nop;
            }
        });
    }
}
