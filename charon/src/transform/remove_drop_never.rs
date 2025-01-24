//! The MIR code often contains variables with type `!` that come from `panic!`s and similar
//! `!`-returning` functions.
//!
//! We want to get rif of these variables since they are never initialized. The only instruction
//! that uses them is `StorageDead`, which is a no-op since there is no corresponding
//! `StorageLive`. We do that in this pass, and the unused local will be removed in
//! `remove_unused_locals`.
use crate::transform::TransformCtx;
use crate::ullbc_ast::*;

use super::ctx::UllbcPass;

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, b: &mut ExprBody) {
        let locals = b.locals.clone();
        b.visit_statements(|st: &mut Statement| {
            // Remove any `StorageDead(x)` where `x` has type `!`. Otherwise leave it unchanged.
            if let RawStatement::StorageDead(var_id) = &st.content
                && locals[*var_id].ty.is_never()
            {
                st.content = RawStatement::Nop;
            }
        });
    }
}
