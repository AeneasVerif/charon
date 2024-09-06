use crate::ids::Vector;
use crate::llbc_ast::*;
use crate::transform::TransformCtx;

use super::ctx::LlbcPass;

pub struct Transform;

impl Transform {
    fn update_statements(locals: &Vector<VarId, Var>, seq: &mut [Statement]) -> Vec<Statement> {
        // Remove double aborts. This can happen when a function call is turned into an `Abort` by
        // `inline_local_panic_functions`.
        if let [Statement {
            content: RawStatement::Abort(_),
            ..
        }, Statement {
            content: second_abort @ RawStatement::Abort(_),
            ..
        }, ..] = seq
        {
            *second_abort = RawStatement::Nop;
            return Vec::new();
        }
        if let [Statement {
            content: RawStatement::Call(call),
            ..
        }, Statement {
            content: second_abort @ RawStatement::Abort(_),
            ..
        }, ..] = seq
            && locals[call.dest.var_id].ty.is_never()
        {
            *second_abort = RawStatement::Nop;
            return Vec::new();
        }

        Vec::new()
    }
}

impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        b.body
            .transform_sequences(&mut |seq| Transform::update_statements(&b.locals, seq))
    }
}