//! Desugar some unary/binary operations and the array repeats to function calls.
//! For instance, we desugar ArrayToSlice from an unop to a function call.
//! This allows a more uniform treatment later on.
//! TODO: actually transform all the unops and binops to function calls?
use crate::expressions::{Rvalue, UnOp};
use crate::llbc_ast::*;
use crate::transform::TransformCtx;
use crate::types::*;

use super::ctx::LlbcPass;

fn transform_st(s: &mut Statement) -> Option<Vec<Statement>> {
    match &s.content {
        // Transform the ArrayToSlice unop
        RawStatement::Assign(p, Rvalue::UnaryOp(UnOp::ArrayToSlice(ref_kind, ty, cg), op)) => {
            // We could avoid the clone operations below if we take the content of
            // the statement. In practice, this shouldn't have much impact.
            let id = match ref_kind {
                RefKind::Mut => AssumedFunId::ArrayToSliceMut,
                RefKind::Shared => AssumedFunId::ArrayToSliceShared,
            };
            let func = FunIdOrTraitMethodRef::mk_assumed(id);
            let generics = GenericArgs::new(
                vec![Region::Erased],
                vec![ty.clone()],
                vec![cg.clone()],
                vec![],
            );
            let func = FnOperand::Regular(FnPtr { func, generics });
            s.content = RawStatement::Call(Call {
                func,
                args: vec![op.clone()],
                dest: p.clone(),
            });

            None
        }
        // Transform the array aggregates to function calls
        RawStatement::Assign(p, Rvalue::Repeat(op, ty, cg)) => {
            // We could avoid the clone operations below if we take the content of
            // the statement. In practice, this shouldn't have much impact.
            let id = AssumedFunId::ArrayRepeat;
            let func = FunIdOrTraitMethodRef::mk_assumed(id);
            let generics = GenericArgs::new(
                vec![Region::Erased],
                vec![ty.clone()],
                vec![cg.clone()],
                vec![],
            );
            let func = FnOperand::Regular(FnPtr { func, generics });
            s.content = RawStatement::Call(Call {
                func,
                args: vec![op.clone()],
                dest: p.clone(),
            });

            None
        }
        _ => None,
    }
}

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        b.body.transform(&mut transform_st);
    }
}
