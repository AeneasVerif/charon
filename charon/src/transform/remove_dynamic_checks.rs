//! # Micro-pass: remove the dynamic checks for array/slice bounds, overflow, and division by zero.
//! Note that from a semantic point of view, an out-of-bound access or a division by zero
//! must lead to a panic in Rust (which is why those checks are always present, even when
//! compiling for release). In our case, we take this into account in the semantics of our
//! array/slice manipulation and arithmetic functions, on the verification side.

use std::mem;

use derive_generic_visitor::*;

use crate::transform::TransformCtx;
use crate::ullbc_ast::{ExprBody, RawStatement, Statement};
use crate::{ast::*, register_error};

use super::ctx::UllbcPass;

/// Whether the value uses the given local in a place.
fn uses_local<T: BodyVisitable>(x: &T, local: LocalId) -> bool {
    struct FoundIt;
    struct UsesLocalVisitor(LocalId);

    impl Visitor for UsesLocalVisitor {
        type Break = FoundIt;
    }
    impl VisitBody for UsesLocalVisitor {
        fn visit_place(&mut self, x: &Place) -> ::std::ops::ControlFlow<Self::Break> {
            if let Some(local_id) = x.as_local() {
                if local_id == self.0 {
                    return ControlFlow::Break(FoundIt);
                }
            }
            self.visit_inner(x)
        }
    }

    x.drive_body(&mut UsesLocalVisitor(local)).is_break()
}

/// Rustc inserts dybnamic checks during MIR lowering. They all end in an `Assert` statement (and
/// this is the only use of this statement).
fn remove_dynamic_checks(
    ctx: &mut TransformCtx,
    _locals: &mut Locals,
    statements: &mut [Statement],
) {
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
                    expected: false,
                    ..
                }),
            ..
        }, rest @ ..]
            if cond == is_zero =>
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
                    expected: false,
                    ..
                }),
            ..
        }, rest @ ..]
            if and_op1 == is_neg_1 && and_op2 == is_min && cond == has_overflow =>
        {
            rest
        }

        // Overflow checks for right/left shift. They can look like:
        //   a := _ as u32; // or another type
        //   b := move a < const 32; // or another constant
        //   assert(move b == true);
        [Statement {
            content: RawStatement::Assign(cast, Rvalue::UnaryOp(UnOp::Cast(_), _)),
            ..
        }, Statement {
            content:
                RawStatement::Assign(
                    has_overflow,
                    Rvalue::BinaryOp(BinOp::Lt, Operand::Move(lhs), Operand::Const(..)),
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
            if cond == has_overflow
                && lhs == cast
                && let Some(cast_local) = cast.as_local()
                && !rest.iter().any(|st| uses_local(st, cast_local)) =>
        {
            rest
        }
        // or like:
        //   b := _ < const 32; // or another constant
        //   assert(move b == true);
        [Statement {
            content:
                RawStatement::Assign(has_overflow, Rvalue::BinaryOp(BinOp::Lt, _, Operand::Const(..))),
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
            if cond == has_overflow =>
        {
            rest
        }

        // Overflow checks for addition/subtraction/multiplication. They look like:
        // ```text
        //   r := x checked.+ y;
        //   assert(move r.1 == false);
        //   ...
        //   z := move r.0;
        // ```
        // We replace that with:
        // ```text
        // z := x + y;
        // ```
        [Statement {
            content:
                RawStatement::Assign(
                    result,
                    rval_op @ Rvalue::BinaryOp(
                        BinOp::CheckedAdd | BinOp::CheckedSub | BinOp::CheckedMul,
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
                    ..
                }),
            ..
        }, rest @ ..]
            if let Some((sub1, ProjectionElem::Field(FieldProjKind::Tuple(..), fid1))) =
                assert_cond.as_projection()
                && fid1.index() == 1
                && result.is_local()
                && sub1 == result =>
        {
            // Switch to the unchecked operation.
            let Rvalue::BinaryOp(binop, ..) = rval_op else {
                unreachable!()
            };
            *binop = match binop {
                BinOp::CheckedAdd => BinOp::Add,
                BinOp::CheckedSub => BinOp::Sub,
                BinOp::CheckedMul => BinOp::Mul,
                _ => unreachable!(),
            };

            // If there's a use of the resulting value, fix it up. There may be none if the result
            // was promoted and computed at compile-time.
            let mut found_use = false;
            for st in rest.iter_mut() {
                if let RawStatement::Assign(_, Rvalue::Use(Operand::Move(assigned))) =
                    &mut st.content
                    && let Some((sub0, ProjectionElem::Field(FieldProjKind::Tuple(..), fid0))) =
                        assigned.as_projection()
                    && fid0.index() == 0
                    && sub0 == result
                {
                    if found_use {
                        register_error!(
                            ctx,
                            st.span,
                            "Double use of a checked binary operation; \
                            the MIR is not in the shape we expected."
                        );
                    }
                    found_use = true;
                    let RawStatement::Assign(_, rval) = &mut st.content else {
                        unreachable!()
                    };
                    // Directly assign the result of the operation to the final place.
                    mem::swap(rval_op, rval);
                }
            }
            // TODO: if !found_use, keep the operation to keep the overflow check.
            rest
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
        b.transform_sequences_fwd(|locals, seq| {
            remove_dynamic_checks(ctx, locals, seq);
            Vec::new()
        });
    }
}
