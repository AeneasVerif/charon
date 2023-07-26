//! # Micro-pass: remove the dynamic checks for array/slice bounds and division by zero.
//! Note that from a semantic point of view, an out-of-bound access or a division by zero
//! must lead to a panic in Rust (which is why those checks are always present, even when
//! compiling for release). In our case, we take this into account in the semantics of our
//! array/slice manipulation and arithmetic functions, on the verification side.

#![allow(dead_code)]

use crate::expressions::MutExprVisitor;
use crate::llbc_ast::{iter_function_bodies, iter_global_bodies};
use crate::llbc_ast::{CtxNames, FunDecls, GlobalDecls, MutAstVisitor, Statement};
use take_mut::take;

struct RemoveDynChecks {}

impl MutExprVisitor for RemoveDynChecks {}

impl MutAstVisitor for RemoveDynChecks {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}

    /// We simply detect sequences of the following shapes, and remove them:
    /// ```
    /// b := copy x < copy y
    /// assert(move b == true)
    /// ```
    ///
    /// ```
    /// b := copy x == const 0
    /// assert(move b == false)
    /// ```
    fn visit_statement(&mut self, s: &mut Statement) {
        if s.content.is_sequence() {
            let (s0, s1) = s.content.as_sequence();
            if s1.content.is_sequence() {
                let (s1, _) = s1.content.as_sequence();
                if s0.content.is_assign() && s1.content.is_assert() {
                    let (dest_p, rv) = s0.content.as_assign();
                    let a = s1.content.as_assert();

                    if rv.is_binary_op() {
                        let (binop, _, _) = rv.as_binary_op();
                        // If the binop is `==`, we don't check that the second
                        // operand is 0...
                        let binop_ok =
                            (binop.is_lt() && a.expected) || (binop.is_eq() && !a.expected);

                        if binop_ok && a.cond.is_move() {
                            let move_p = a.cond.as_move();

                            if move_p == dest_p {
                                // Eliminate the first two statements
                                take(s, |s| {
                                    let (_, s1) = s.content.to_sequence();
                                    let (_, s2) = s1.content.to_sequence();
                                    *s2
                                });
                                self.visit_statement(s);
                                // Return so as not to take the default branch
                                return;
                            }
                        }
                    }
                }
            }
        }
        // Dive in.
        // Make sure we eliminate all the asserts.
        assert!(!s.content.is_assert());
        self.default_visit_raw_statement(&mut s.content);
    }
}

pub fn transform(fmt_ctx: &CtxNames<'_>, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to remove the dynamic checks: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
        let mut visitor = RemoveDynChecks {};
        visitor.visit_statement(&mut b.body);
        trace!(
            "# After we removed the dynamic checks: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
    }
}
