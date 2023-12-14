//! # Micro-pass: remove the dynamic checks for array/slice bounds and division by zero.
//! Note that from a semantic point of view, an out-of-bound access or a division by zero
//! must lead to a panic in Rust (which is why those checks are always present, even when
//! compiling for release). In our case, we take this into account in the semantics of our
//! array/slice manipulation and arithmetic functions, on the verification side.
use crate::formatter::{Formatter, IntoFormatter};
use crate::llbc_ast::*;
use crate::translate_ctx::{error_assert_then, TransCtx};
use crate::types::*;
use crate::values::*;
use take_mut::take;

struct RemoveDynChecks<'tcx, 'ctx, 'a> {
    /// We use the context for debugging and error reporting
    ctx: &'a mut TransCtx<'tcx, 'ctx>,
}

impl<'tcx, 'ctx, 'a> MutTypeVisitor for RemoveDynChecks<'tcx, 'ctx, 'a> {}
impl<'tcx, 'ctx, 'a> MutExprVisitor for RemoveDynChecks<'tcx, 'ctx, 'a> {}

/// Check that a statement is exactly:
/// ```text
/// assert(move p == expected)
/// ```
fn is_assert_move(p: &Place, s: &Statement, expected: bool) -> bool {
    if let RawStatement::Assert(Assert {
        cond: Operand::Move(ap),
        expected: aexpected,
    }) = &s.content
    {
        return ap == p && *aexpected == expected;
    }
    // Default
    false
}

impl<'tcx, 'ctx, 'a> RemoveDynChecks<'tcx, 'ctx, 'a> {
    /// Return [true] if we simplified the statements, [false] otherwise.
    /// TODO: we need a way of simplifying all this...
    ///
    /// We simply detect sequences of the following shapes, and remove them:
    /// # 1. Division/remainder/multiplication
    /// ======================================
    /// ```text
    /// b := copy x == const 0
    /// assert(move b == false)
    /// ```
    ///
    /// **Special case**: division/remainder for signed integers. Rust checks
    /// that we don't have, for instance: `i32::min / (-1)`:
    /// ```text
    /// b_y := y == const (-1)
    /// b_x := x == const INT::min
    /// b := move (b_y) & move (b_x)
    /// assert(move b == false)
    /// z := x / y
    /// ```
    ///
    /// # 2. Addition/substraction/multiplication.
    /// ==========================================
    /// In release mode, the rust compiler inserts assertions only inside the
    /// body of global constants.
    /// ```text
    /// r := x + y;
    /// assert(move r.1 == false);
    /// z := move r.0;
    /// ```
    ///
    /// # 3. Arrays/slices
    /// ==================
    /// ```text
    /// l := len(a)
    /// b := copy x < copy l
    /// assert(move b == true)
    /// ```
    ///
    /// # Shifts
    /// ========
    /// ```text
    /// x := ...;
    /// b := move x < const 32; // or another constant
    /// assert(move b == true);
    /// ```
    fn simplify(&mut self, s: &mut Statement) -> bool {
        if let RawStatement::Sequence(s0, s1) = &s.content {
            if let RawStatement::Sequence(s1, s2) = &s1.content {
                // Arrays/Slices
                if let (
                    // s0 should be: `l := len(a)`
                    RawStatement::Assign(dest_l_p, Rvalue::Len(..)),
                    // s1 should be: `b := copy x < copy l`
                    RawStatement::Assign(
                        dest_b_p,
                        Rvalue::BinaryOp(BinOp::Lt, _, Operand::Copy(l_op_place)),
                    ),
                    // s2
                    RawStatement::Sequence(s2, _),
                ) = (&s0.content, &s1.content, &s2.content)
                {
                    // s2 should be: `assert(move b == true)`
                    if dest_l_p == l_op_place && is_assert_move(dest_b_p, s2, true) {
                        // Eliminate the first three statements
                        take(s, |s| {
                            let (_, s1) = s.content.to_sequence();
                            let (_, s2) = s1.content.to_sequence();
                            let (_, s3) = s2.content.to_sequence();
                            *s3
                        });
                        // A simplification happened
                        return true;
                    }
                }
                // Shift left
                else if let (
                    // s0 should be an assignment
                    RawStatement::Assign(dest_x_p, _),
                    // s1 should be: `b := copy x < const ...`
                    RawStatement::Assign(
                        dest_b_p,
                        Rvalue::BinaryOp(BinOp::Lt, Operand::Move(x_place), Operand::Const(..)),
                    ),
                    RawStatement::Sequence(s2, _),
                ) = (&s0.content, &s1.content, &s2.content)
                {
                    // s2 should be: `assert(move b == true)`
                    if dest_x_p == x_place && is_assert_move(dest_b_p, s2, true) {
                        // Eliminate the first three statements
                        take(s, |s| {
                            let (_, s1) = s.content.to_sequence();
                            let (_, s2) = s1.content.to_sequence();
                            let (_, s3) = s2.content.to_sequence();
                            *s3
                        });
                        // A simplification happened
                        return true;
                    }
                }
                // Signed division and remainder
                // TODO: check x_op and y_op
                else if let (
                    // b_y_p := y == (-1)
                    RawStatement::Assign(
                        b_y_p,
                        Rvalue::BinaryOp(
                            BinOp::Eq,
                            _y_op,
                            Operand::Const(ConstantExpr {
                                value: RawConstantExpr::Literal(Literal::Scalar(_)),
                                ty: _,
                            }),
                        ),
                    ),
                    // b_x_p := x == INT::min
                    // TODO: check min_op
                    RawStatement::Assign(b_x_p, Rvalue::BinaryOp(BinOp::Eq, _x_op, _min_op)),
                    // s2
                    // s3
                    RawStatement::Sequence(s2, s3),
                ) = (&s0.content, &s1.content, &s2.content)
                {
                    if let RawStatement::Sequence(s3, s4) = &s3.content {
                        if let (
                            // b := move (b_y) & move (b_x)
                            RawStatement::Assign(
                                b_p,
                                Rvalue::BinaryOp(
                                    BinOp::BitAnd,
                                    Operand::Move(b_y_p1),
                                    Operand::Move(b_x_p1),
                                ),
                            ),
                            // assert(move b == false)
                            RawStatement::Assert(Assert {
                                cond: Operand::Move(b_p_1),
                                expected: false,
                            }),
                            // z := x / y;
                            // ...
                            RawStatement::Sequence(s4, _),
                        ) = (&s2.content, &s3.content, &s4.content)
                        {
                            if b_x_p == b_x_p1
                                && b_y_p1 == b_y_p
                                && b_p == b_p_1
                                // x := x / y
                                && matches!(
                                    &s4.content,
                                    RawStatement::Assign(
                                        _,
                                        Rvalue::BinaryOp(BinOp::Div | BinOp::Rem, _, _)
                                    )
                                )
                            {
                                // Eliminate the first 4 statements
                                take(s, |s| {
                                    let (_, s1) = s.content.to_sequence();
                                    let (_, s2) = s1.content.to_sequence();
                                    let (_, s3) = s2.content.to_sequence();
                                    let (_, s4) = s3.content.to_sequence();
                                    *s4
                                });
                                return true;
                            }
                        }
                    }
                }
                // Division/remainder/addition/etc.
                else if let RawStatement::Assign(dest_p, Rvalue::BinaryOp(binop, _, _)) =
                    &s0.content
                {
                    // We don't check that the second operand is 0 in
                    // case we are in the division/remainder case
                    if matches!(binop, BinOp::Eq) && is_assert_move(dest_p, s1, false) {
                        // This should be the division/remainder case
                        // Eliminate the first two statements
                        take(s, |s| {
                            let (_, s1) = s.content.to_sequence();
                            let (_, s2) = s1.content.to_sequence();
                            *s2
                        });
                        // We performed a change
                        return true;
                    } else if let (
                        RawStatement::Assert(Assert {
                            cond: Operand::Move(move_p),
                            ..
                        }),
                        RawStatement::Sequence(s2, _),
                    ) = (&s1.content, &s2.content)
                    {
                        // TODO: the last statement is not necessarily a sequence
                        // This should be the addition/subtraction/etc. case
                        error_assert_then!(
                            self.ctx,
                            s0.meta.span.rust_span,
                            matches!(binop, BinOp::Add | BinOp::Sub | BinOp::Mul),
                            // TODO: we could replace the whole statement with an "ERROR" statement
                            // A simplification should have happened but was missed:
                            // stop the simplification here.
                            return true,
                            format!(
                                "Unexpected binop while removing dynamic checks: {:?}",
                                binop
                            )
                        );

                        if let RawStatement::Assign(_, Rvalue::Use(Operand::Move(move_p1))) =
                            &s2.content
                        {
                            // move_p should be: r.1
                            // move_p1 should be: r.0
                            if move_p.var_id == move_p1.var_id
                                && move_p.projection.len() == 1
                                && move_p1.projection.len() == 1
                            {
                                if let (
                                    ProjectionElem::Field(FieldProjKind::Tuple(..), fid0),
                                    ProjectionElem::Field(FieldProjKind::Tuple(..), fid1),
                                ) = (&move_p.projection[0], &move_p1.projection[0])
                                {
                                    use crate::id_vector::ToUsize;
                                    if fid0.to_usize() == 1 && fid1.to_usize() == 0 {
                                        // Collapse into one assignment
                                        take(s, |s| {
                                            let (s0, s1) = s.content.to_sequence();
                                            let (_, s2) = s1.content.to_sequence();
                                            let (s2, s3) = s2.content.to_sequence();
                                            let (_, op) = s0.content.to_assign();
                                            let (dest, _) = s2.content.to_assign();
                                            let meta0 = s0.meta;
                                            let s0 = RawStatement::Assign(dest, op);
                                            let s0 = Statement {
                                                meta: meta0,
                                                content: s0,
                                            };
                                            Statement {
                                                meta: s2.meta,
                                                content: RawStatement::Sequence(Box::new(s0), s3),
                                            }
                                        });
                                        // A simplification happened
                                        return true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        };

        // No simplification
        false
    }
}

impl<'tcx, 'ctx, 'a> MutAstVisitor for RemoveDynChecks<'tcx, 'ctx, 'a> {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}

    fn visit_statement(&mut self, s: &mut Statement) {
        // Simplify
        if self.simplify(s) {
            // A simplification happened: visit again the updated statement
            self.visit_statement(s)
        } else {
            // No simplification: dive in.
            // Make sure we eliminated all the asserts and all the `len`
            error_assert_then!(
                self.ctx,
                s.meta.span.rust_span,
                !s.content.is_assert(),
                // Return so as to stop the exploration
                return,
                "Found an assert which was not simplified"
            );
            if s.content.is_assign() {
                let (_, rv) = s.content.as_assign();
                error_assert_then!(
                    self.ctx,
                    s.meta.span.rust_span,
                    !rv.is_len(),
                    // Return so as to stop the exploration
                    return,
                    "Found an occurrence of Len which was not simplified"
                );
            }
            self.default_visit_raw_statement(&mut s.content);
        }
    }
}

pub fn transform(ctx: &mut TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    ctx.iter_bodies(funs, globals, |ctx, name, b| {
        let fmt_ctx = ctx.into_fmt();
        trace!(
            "# About to remove the dynamic checks: {}:\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );
        let mut visitor = RemoveDynChecks { ctx };
        visitor.visit_statement(&mut b.body);
        let fmt_ctx = ctx.into_fmt();
        trace!(
            "# After we removed the dynamic checks: {}:\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );
    })
}
