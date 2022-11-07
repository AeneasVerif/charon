//! In the MIR AST, it seems `assert` are introduced to check preconditions
//! (for the binops for example). The `assert!` introduced by the user
//! introduce `if ... then { panic!(...) } else { ...}`.
//! This pass introduces `assert` instead in order to make the code shorter.

use take_mut::take;

use crate::{
    llbc_ast::{Assert, CtxNames, FunDecls, GlobalDecls, Match, RawStatement, Statement},
    ullbc_ast::{iter_function_bodies, iter_global_bodies},
};
use std::iter::FromIterator;

fn transform_st(mut st: Statement) -> Statement {
    st.content = match st.content {
        RawStatement::Assign(p, rv) => RawStatement::Assign(p, rv),
        RawStatement::FakeRead(p) => RawStatement::FakeRead(p),
        RawStatement::SetDiscriminant(p, vid) => RawStatement::SetDiscriminant(p, vid),
        RawStatement::Drop(p) => RawStatement::Drop(p),
        RawStatement::Assert(assert) => RawStatement::Assert(assert),
        RawStatement::Call(call) => RawStatement::Call(call),
        RawStatement::Panic => RawStatement::Panic,
        RawStatement::Return => RawStatement::Return,
        RawStatement::Break(i) => RawStatement::Break(i),
        RawStatement::Continue(i) => RawStatement::Continue(i),
        RawStatement::Nop => RawStatement::Nop,
        RawStatement::Match(mtch) => {
            match mtch {
                Match::If(op, st1, st2) => {
                    let st2 = Box::new(transform_st(*st2));

                    // Check if the first statement is a panic: if yes, replace
                    // the if .. then ... else ... by an assertion.
                    if st1.content.is_panic() {
                        let st1 = Statement::new(
                            st1.meta,
                            RawStatement::Assert(Assert {
                                cond: op,
                                expected: false,
                            }),
                        );
                        let st1 = Box::new(st1);

                        RawStatement::Sequence(st1, st2)
                    } else {
                        let mtch = Match::If(op, Box::new(transform_st(*st1)), st2);
                        RawStatement::Match(mtch)
                    }
                }
                Match::SwitchInt(op, int_ty, targets, otherwise) => {
                    let targets =
                        Vec::from_iter(targets.into_iter().map(|(v, e)| (v, transform_st(e))));
                    let otherwise = transform_st(*otherwise);
                    let mtch = Match::SwitchInt(op, int_ty, targets, Box::new(otherwise));
                    RawStatement::Match(mtch)
                }
                Match::Match(_, _) => {
                    // This variant is introduced in a subsequent pass
                    unreachable!();
                }
            }
        }
        RawStatement::Loop(loop_body) => RawStatement::Loop(Box::new(transform_st(*loop_body))),
        RawStatement::Sequence(st1, st2) => {
            RawStatement::Sequence(Box::new(transform_st(*st1)), Box::new(transform_st(*st2)))
        }
    };

    st
}

pub fn transform<'ctx>(fmt_ctx: &CtxNames<'ctx>, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to reconstruct asserts in decl: {name}\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
        take(&mut b.body, transform_st);
    }
}
