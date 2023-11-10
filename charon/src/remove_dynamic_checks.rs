//! # Micro-pass: remove the dynamic checks for array/slice bounds and division by zero.
//! Note that from a semantic point of view, an out-of-bound access or a division by zero
//! must lead to a panic in Rust (which is why those checks are always present, even when
//! compiling for release). In our case, we take this into account in the semantics of our
//! array/slice manipulation and arithmetic functions, on the verification side.

#![allow(dead_code)]

use crate::formatter::Formatter;
use crate::llbc_ast::*;
use crate::translate_ctx::TransCtx;
use crate::types::*;
use take_mut::take;

struct RemoveDynChecks {}

impl MutTypeVisitor for RemoveDynChecks {}
impl MutExprVisitor for RemoveDynChecks {}

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

impl MutAstVisitor for RemoveDynChecks {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}

    /// We simply detect sequences of the following shapes, and remove them:
    /// # 1. Division/remainder/multiplication
    /// ```text
    /// b := copy x == const 0
    /// assert(move b == false)
    /// ```
    ///
    /// # 2. Addition/substraction/multiplication.
    /// In release mode, the rust compiler inserts assertions only inside the
    /// body of global constants.
    /// ```text
    /// r := x + y;
    /// assert(move r.1 == false);
    /// z := move r.0;
    /// ```
    ///
    /// # 3. Arrays/slices
    /// ```text
    /// l := len(a)
    /// b := copy x < copy l
    /// assert(move b == true)
    /// ```
    ///
    /// # Shifts
    /// ```text
    /// x := ...;
    /// b := move x < const 32; // or another constant
    /// assert(move b == true);
    /// ```
    fn visit_statement(&mut self, s: &mut Statement) {
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
                        self.visit_statement(s);
                        // Return so as not to take the default branch
                        return;
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
                        self.visit_statement(s);
                        // Return so as not to take the default branch
                        return;
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
                        self.visit_statement(s);
                        // Return so as not to take the default branch
                        return;
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
                        assert!(
                            matches!(binop, BinOp::Add | BinOp::Sub | BinOp::Mul),
                            "{:?}",
                            binop
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
                                match (&move_p.projection[0], &move_p1.projection[0]) {
                                    (
                                        ProjectionElem::Field(FieldProjKind::Tuple(..), fid0),
                                        ProjectionElem::Field(FieldProjKind::Tuple(..), fid1),
                                    ) => {
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
                                                    content: RawStatement::Sequence(
                                                        Box::new(s0),
                                                        s3,
                                                    ),
                                                }
                                            });
                                            self.visit_statement(s);
                                            // Return so as not to take the default branch
                                            return;
                                        }
                                    }
                                    _ => (),
                                }
                            }
                        }
                    }
                }
            }
        }
        // Dive in.
        // Make sure we eliminate all the asserts and all the len
        assert!(!s.content.is_assert());
        if s.content.is_assign() {
            let (_, rv) = s.content.as_assign();
            assert!(!rv.is_len());
        }
        self.default_visit_raw_statement(&mut s.content);
    }
}

pub fn transform(ctx: &TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to remove the dynamic checks: {name}:\n{}",
            ctx.format_object(&*b)
        );
        let mut visitor = RemoveDynChecks {};
        visitor.visit_statement(&mut b.body);
        trace!(
            "# After we removed the dynamic checks: {name}:\n{}",
            ctx.format_object(&*b)
        );
    }
}
