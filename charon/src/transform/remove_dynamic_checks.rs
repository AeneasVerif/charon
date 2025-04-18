//! # Micro-pass: remove the dynamic checks for array/slice bounds, overflow, and division by zero.
//! Note that from a semantic point of view, an out-of-bound access or a division by zero
//! must lead to a panic in Rust (which is why those checks are always present, even when
//! compiling for release). In our case, we take this into account in the semantics of our
//! array/slice manipulation and arithmetic functions, on the verification side.

use crate::ast::*;
use crate::transform::TransformCtx;
use crate::ullbc_ast::{ExprBody, RawStatement, Statement};

use super::ctx::UllbcPass;

/// Rustc inserts dybnamic checks during MIR lowering. They all end in an `Assert` statement (and
/// this is the only use of this statement).
fn remove_dynamic_checks(_ctx: &mut TransformCtx, statements: &mut [Statement]) {
    // We return the statements we want to keep, which must be a prefix of `block.statements`.
    let statements_to_keep = match statements {
        // Bounds checks for slices. They look like:
        //   l := ptr_metadata(copy a)
        //   b := copy x < copy l
        //   assert(move b == true)
        [Statement {
            content:
                RawStatement::Assign(len, Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(len_op))),
            ..
        }, Statement {
            content:
                RawStatement::Assign(
                    is_in_bounds,
                    Rvalue::BinaryOp(BinOp::Lt, _, Operand::Copy(lt_op2)),
                ),
            ..
        }, Statement {
            content:
                RawStatement::Assert(Assert {
                    cond: Operand::Move(cond),
                    expected: true,
                    ..
                }),
            ..
        }, rest @ ..]
            if lt_op2 == len && cond == is_in_bounds && len_op.ty().is_ref() =>
        {
            rest
        }
        // Sometimes that instead looks like:
        //   a := &raw const *z
        //   l := ptr_metadata(move a)
        //   b := copy x < copy l
        //   assert(move b == true)
        [Statement {
            content: RawStatement::Assign(reborrow, Rvalue::RawPtr(_, RefKind::Shared)),
            ..
        }, Statement {
            content:
                RawStatement::Assign(len, Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Move(len_op))),
            ..
        }, Statement {
            content:
                RawStatement::Assign(
                    is_in_bounds,
                    Rvalue::BinaryOp(BinOp::Lt, _, Operand::Copy(lt_op2)),
                ),
            ..
        }, Statement {
            content:
                RawStatement::Assert(Assert {
                    cond: Operand::Move(cond),
                    expected: true,
                    ..
                }),
            ..
        }, rest @ ..]
            if reborrow == len_op && lt_op2 == len && cond == is_in_bounds =>
        {
            rest
        }

        // Bounds checks for arrays. They look like:
        //   b := copy x < const _
        //   assert(move b == true)
        [Statement {
            content:
                RawStatement::Assign(is_in_bounds, Rvalue::BinaryOp(BinOp::Lt, _, Operand::Const(_))),
            ..
        }, Statement {
            content:
                RawStatement::Assert(Assert {
                    cond: Operand::Move(cond),
                    expected: true,
                    ..
                }),
            ..
        }, rest @ ..]
            if cond == is_in_bounds =>
        {
            rest
        }

        // Zero checks for division and remainder. They look like:
        //   b := copy x == const 0
        //   assert(move b == false)
        [Statement {
            content:
                RawStatement::Assign(is_zero, Rvalue::BinaryOp(BinOp::Eq, _, Operand::Const(_zero))),
            ..
        }, Statement {
            content:
                RawStatement::Assert(Assert {
                    cond: Operand::Move(cond),
                    expected,
                    ..
                }),
            ..
        }, rest @ ..]
            if cond == is_zero && *expected == false =>
        {
            rest
        }

        // Overflow checks for signed division and remainder. They look like:
        //   is_neg_1 := y == (-1)
        //   is_min := x == INT::min
        //   has_overflow := move (is_neg_1) & move (is_min)
        //   assert(move has_overflow == false)
        [Statement {
            content: RawStatement::Assign(is_neg_1, Rvalue::BinaryOp(BinOp::Eq, _y_op, _minus_1)),
            ..
        }, Statement {
            content: RawStatement::Assign(is_min, Rvalue::BinaryOp(BinOp::Eq, _x_op, _int_min)),
            ..
        }, Statement {
            content:
                RawStatement::Assign(
                    has_overflow,
                    Rvalue::BinaryOp(BinOp::BitAnd, Operand::Move(and_op1), Operand::Move(and_op2)),
                ),
            ..
        }, Statement {
            content:
                RawStatement::Assert(Assert {
                    cond: Operand::Move(cond),
                    expected,
                    ..
                }),
            ..
        }, rest @ ..]
            if and_op1 == is_neg_1
                && and_op2 == is_min
                && cond == has_overflow
                && *expected == false =>
        {
            rest
        }

        // Overflow checks for right/left shift. They can look like:
        //   x := ...;
        //   b := move x < const 32; // or another constant
        //   assert(move b == true);
        [Statement {
            content: RawStatement::Assign(x, _),
            ..
        }, Statement {
            content:
                RawStatement::Assign(
                    has_overflow,
                    Rvalue::BinaryOp(BinOp::Lt, Operand::Move(lt_op2), Operand::Const(..)),
                ),
            ..
        }, Statement {
            content:
                RawStatement::Assert(Assert {
                    cond: Operand::Move(cond),
                    expected,
                    ..
                }),
            ..
        }, rest @ ..]
            if lt_op2 == x && cond == has_overflow && *expected == true =>
        {
            rest
        }
        // They can also look like:
        //   b := const c < const 32; // or another constant
        //   assert(move b == true);
        [Statement {
            content:
                RawStatement::Assign(
                    has_overflow,
                    Rvalue::BinaryOp(BinOp::Lt, Operand::Const(..), Operand::Const(..)),
                ),
            ..
        }, Statement {
            content:
                RawStatement::Assert(Assert {
                    cond: Operand::Move(cond),
                    expected,
                    ..
                }),
            ..
        }, rest @ ..]
            if cond == has_overflow && *expected == true =>
        {
            rest
        }

        // Overflow checks for addition/subtraction/multiplication. They look like:
        //   r := x checked.+ y;
        //   assert(move r.1 == false);
        // They only happen in constants because we compile with `-C opt-level=3`. They span two
        // blocks so we remove them in a later pass.
        [Statement {
            content:
                RawStatement::Assign(
                    result,
                    Rvalue::BinaryOp(BinOp::CheckedAdd | BinOp::CheckedSub | BinOp::CheckedMul, ..),
                ),
            ..
        }, Statement {
            content:
                RawStatement::Assert(Assert {
                    cond: Operand::Move(cond),
                    expected,
                    ..
                }),
            ..
        }, ..]
            if result.is_local()
                && let Some((sub, ProjectionElem::Field(FieldProjKind::Tuple(2), p_id))) =
                    cond.as_projection()
                && sub.is_local()
                && cond.local_id() == result.local_id()
                && p_id.index() == 1
                && *expected == false =>
        {
            // We leave this assert intact; it will be simplified in
            // [`remove_arithmetic_overflow_checks`].
            return;
        }

        _ => return,
    };

    // Remove the statements.
    let keep_len = statements_to_keep.len();
    for i in 0..statements.len() - keep_len {
        statements[i].content = RawStatement::Nop;
    }
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, ctx: &mut TransformCtx, b: &mut ExprBody) {
        for block in b.body.iter_mut() {
            block.transform_sequences(|seq| {
                remove_dynamic_checks(ctx, seq);
                Vec::new()
            });
        }
    }
}
