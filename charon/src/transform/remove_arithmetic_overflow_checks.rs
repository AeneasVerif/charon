//! # Micro-pass: remove the overflow checks for arithmetic operations we couldn't remove in
//! [`remove_dynamic_checks`]. See comments there for more details.
use crate::transform::TransformCtx;
use crate::ullbc_ast::*;

use super::ctx::UllbcPass;

pub struct Transform;

impl Transform {
    /// After `remove_dynamic_checks`, the only remaining dynamic checks are overflow checks. We
    /// couldn't remove them in ullbc because the generated code spans two basic blocks. They are
    /// inserted only in constants since we otherwise compile in release mode. These assertions
    /// look like:
    /// ```text
    /// r := x checked.+ y;
    /// assert(move r.1 == false);
    /// z := move r.0;
    /// ```
    /// We replace that with:
    /// ```text
    /// z := x + y;
    /// ```
    fn update_statements(seq: &mut [Statement]) {
        if let [Statement {
            content:
                RawStatement::Assign(
                    binop,
                    Rvalue::BinaryOp(
                        op @ (BinOp::CheckedAdd | BinOp::CheckedSub | BinOp::CheckedMul),
                        _,
                        _,
                    ),
                ),
            ..
        }, Statement {
            content:
                RawStatement::Assert(Assert {
                    cond: Operand::Move(assert_cond),
                    expected: false,
                }),
            ..
        }, Statement {
            content: RawStatement::Assign(final_value, Rvalue::Use(Operand::Move(assigned))),
            ..
        }, ..] = seq
        {
            // assigned should be: binop.0
            // assert_cond should be: binop.1
            if let (
                [ProjectionElem::Field(FieldProjKind::Tuple(..), fid0)],
                [ProjectionElem::Field(FieldProjKind::Tuple(..), fid1)],
            ) = (
                assigned.projection.as_slice(),
                assert_cond.projection.as_slice(),
            ) {
                if assert_cond.var_id == binop.var_id
                    && assigned.var_id == binop.var_id
                    && binop.projection.len() == 0
                    && fid0.index() == 0
                    && fid1.index() == 1
                {
                    // Switch to the unchecked operation.
                    *op = match op {
                        BinOp::CheckedAdd => BinOp::Add,
                        BinOp::CheckedSub => BinOp::Sub,
                        BinOp::CheckedMul => BinOp::Mul,
                        _ => unreachable!(),
                    };
                    // Assign to the correct value in the first statement.
                    std::mem::swap(binop, final_value);
                    // Remove the other two statements.
                    seq[1].content = RawStatement::Nop;
                    seq[2].content = RawStatement::Nop;
                }
            }
        }
    }
}

impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        b.transform_sequences(&mut |_, seq| {
            Transform::update_statements(seq);
            Vec::new()
        })
    }
}
