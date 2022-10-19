//! In the MIR AST, it seems `assert` are introduced to check preconditions
//! (for the binops for example). The `assert!` introduced by the user
//! introduce `if ... then { panic!(...) } else { ...}`.
//! This pass introduces `assert` instead in order to make the code shorter.

use take_mut::take;

use crate::{
    llbc_ast::{Assert, CtxNames, FunDecls, GlobalDecls, Statement, SwitchTargets},
    ullbc_ast::{iter_function_bodies, iter_global_bodies},
};
use std::iter::FromIterator;

fn transform_st(st: Statement) -> Statement {
    match st {
        Statement::Assign(p, rv) => Statement::Assign(p, rv),
        Statement::AssignGlobal(p, g) => Statement::AssignGlobal(p, g),
        Statement::FakeRead(p) => Statement::FakeRead(p),
        Statement::SetDiscriminant(p, vid) => Statement::SetDiscriminant(p, vid),
        Statement::Drop(p) => Statement::Drop(p),
        Statement::Assert(assert) => Statement::Assert(assert),
        Statement::Call(call) => Statement::Call(call),
        Statement::Panic => Statement::Panic,
        Statement::Return => Statement::Return,
        Statement::Break(i) => Statement::Break(i),
        Statement::Continue(i) => Statement::Continue(i),
        Statement::Nop => Statement::Nop,
        Statement::Switch(op, targets) => {
            match targets {
                SwitchTargets::If(st1, st2) => {
                    let st2 = Box::new(transform_st(*st2));

                    // Check if the first statement is a panic: if yes, replace
                    // the if .. then ... else ... by an assertion.
                    if st1.is_panic() {
                        let st1 = Statement::Assert(Assert {
                            cond: op,
                            expected: false,
                        });
                        let st1 = Box::new(st1);

                        Statement::Sequence(st1, st2)
                    } else {
                        let targets = SwitchTargets::If(Box::new(transform_st(*st1)), st2);
                        Statement::Switch(op, targets)
                    }
                }
                SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                    let targets =
                        Vec::from_iter(targets.into_iter().map(|(v, e)| (v, transform_st(e))));
                    let otherwise = transform_st(*otherwise);
                    let targets = SwitchTargets::SwitchInt(int_ty, targets, Box::new(otherwise));
                    Statement::Switch(op, targets)
                }
            }
        }
        Statement::Loop(loop_body) => Statement::Loop(Box::new(transform_st(*loop_body))),
        Statement::Sequence(st1, st2) => {
            Statement::Sequence(Box::new(transform_st(*st1)), Box::new(transform_st(*st2)))
        }
    }
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
