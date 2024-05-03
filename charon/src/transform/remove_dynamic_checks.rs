//! # Micro-pass: remove the dynamic checks for array/slice bounds, overflow, and division by zero.
//! Note that from a semantic point of view, an out-of-bound access or a division by zero
//! must lead to a panic in Rust (which is why those checks are always present, even when
//! compiling for release). In our case, we take this into account in the semantics of our
//! array/slice manipulation and arithmetic functions, on the verification side.

use crate::formatter::{Formatter, IntoFormatter};
use crate::llbc_ast::{BinOp, FieldProjKind, Operand, ProjectionElem, Rvalue};
use crate::translate_ctx::{register_error_or_panic, TransCtx};
use crate::ullbc_ast::{BlockData, RawStatement, RawTerminator, Statement};

/// Rustc inserts dybnamic checks during MIR lowering. They all end in an `Assert` terminator (and
/// this is the only use of this terminator).
fn remove_dynamic_checks(ctx: &mut TransCtx, block: &mut BlockData) {
    let RawTerminator::Assert {
        cond: Operand::Move(cond),
        expected,
        target,
    } = &block.terminator.content else { return };

    // We return the statements we want to keep, which must be a prefix of `block.statements`.
    let statements_to_keep = match block.statements.as_mut_slice() {
        // Bounds checks for arrays/slices. They look like:
        //   l := len(a)
        //   b := copy x < copy l
        //   assert(move b == true)
        [rest @ .., Statement {
            content: RawStatement::Assign(len, Rvalue::Len(..)),
            ..
        }, Statement {
            content:
                RawStatement::Assign(
                    is_in_bounds,
                    Rvalue::BinaryOp(BinOp::Lt, _, Operand::Copy(lt_op2)),
                ),
            ..
        }] if lt_op2 == len && cond == is_in_bounds && *expected == true => rest,

        // Zero checks for division and remainder. They look like:
        //   b := copy x == const 0
        //   assert(move b == false)
        [rest @ .., Statement {
            content: RawStatement::Assign(is_zero, Rvalue::BinaryOp(BinOp::Eq, _, Operand::Const(_zero))),
            ..
        }] if cond == is_zero && *expected == false => rest,

        // Overflow checks for signed division and remainder. They look like:
        //   is_neg_1 := y == (-1)
        //   is_min := x == INT::min
        //   has_overflow := move (is_neg_1) & move (is_min)
        //   assert(move has_overflow == false)
        [rest @ .., Statement {
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
        }] if and_op1 == is_neg_1
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
        [rest @ .., Statement {
            content: RawStatement::Assign(x, _),
            ..
        }, Statement {
            content:
                RawStatement::Assign(
                    has_overflow,
                    Rvalue::BinaryOp(BinOp::Lt, Operand::Move(lt_op2), Operand::Const(..)),
                ),
            ..
        }] if lt_op2 == x && cond == has_overflow && *expected == true => rest,
        // They can also look like:
        //   b := const c < const 32; // or another constant
        //   assert(move b == true);
        [rest @ .., Statement {
            content:
                RawStatement::Assign(
                    has_overflow,
                    Rvalue::BinaryOp(BinOp::Lt, Operand::Const(..), Operand::Const(..)),
                ),
            ..
        }] if cond == has_overflow && *expected == true => rest,

        // Overflow checks for addition/subtraction/multiplication. They look like:
        //   r := x checked.+ y;
        //   assert(move r.1 == false);
        // They only happen in constants because we compile with `-C opt-level=3`. They're tricky
        // to remove so we leave them for now.
        [.., Statement {
            content:
                RawStatement::Assign(result, Rvalue::BinaryOp(BinOp::CheckedAdd | BinOp::CheckedSub | BinOp::CheckedMul, ..)),
            ..
        }] if cond.var_id == result.var_id
            && result.projection.is_empty()
            && let [ProjectionElem::Field(FieldProjKind::Tuple(2), p_id)] = cond.projection.as_slice()
            && p_id.index() == 1
            && *expected == false =>
        {
            // We leave this assert intact.
            return
        }

        _ => {
            // This can happen for the dynamic checks we don't handle, corresponding to the
            // `rustc_middle::mir::AssertKind` variants `ResumedAfterReturn`, `ResumedAfterPanic`
            // and `MisalignedPointerDereference`.
            let fmt_ctx = ctx.into_fmt();
            let msg = format!("Found an `assert` we don't recognize:\n{}", block.fmt_with_ctx("", &fmt_ctx));
            register_error_or_panic!(
                ctx,
                block.terminator.meta.span,
                msg
            );
            return
        }
    };

    // Remove the statements and replace the assert with a goto.
    let len = statements_to_keep.len();
    block.statements.truncate(len);
    block.terminator.content = RawTerminator::Goto { target: *target };
}

pub fn transform(ctx: &mut TransCtx) {
    // Slightly annoying: we have to clone because of borrowing issues
    let mut fun_decls = ctx.fun_decls.clone();
    let mut global_decls = ctx.global_decls.clone();

    ctx.iter_bodies(&mut fun_decls, &mut global_decls, |ctx, name, b| {
        let fmt_ctx = ctx.into_fmt();
        trace!(
            "# About to remove the dynamic checks: {}:\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );

        for block in b.body.iter_mut() {
            remove_dynamic_checks(ctx, block);
        }

        let fmt_ctx = ctx.into_fmt();
        trace!(
            "# After we removed the dynamic checks: {}:\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );
    });

    ctx.fun_decls = fun_decls;
    ctx.global_decls = global_decls;
}
