//! In the MIR AST, it seems `assert` are introduced to check preconditions
//! (for the binops for example). The `assert!` introduced by the user
//! introduce `if ... then { panic!(...) } else { ...}`.
//! This pass introduces `assert` instead in order to make the code shorter.

use crate::cfim_ast::*;
use hashlink::linked_hash_map::LinkedHashMap;
use std::iter::FromIterator;

fn simplify_st(st: Statement) -> Statement {
    match st {
        Statement::Assign(p, rv) => Statement::Assign(p, rv),
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
                    let st2 = Box::new(simplify_st(*st2));

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
                        let targets = SwitchTargets::If(Box::new(simplify_st(*st1)), st2);
                        Statement::Switch(op, targets)
                    }
                }
                SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                    let targets = LinkedHashMap::from_iter(
                        targets.into_iter().map(|(v, e)| (v, simplify_st(e))),
                    );
                    let otherwise = simplify_st(*otherwise);
                    let targets = SwitchTargets::SwitchInt(int_ty, targets, Box::new(otherwise));
                    Statement::Switch(op, targets)
                }
            }
        }
        Statement::Loop(loop_body) => Statement::Loop(Box::new(simplify_st(*loop_body))),
        Statement::Sequence(st1, st2) => {
            Statement::Sequence(Box::new(simplify_st(*st1)), Box::new(simplify_st(*st2)))
        }
    }
}
fn simplify_def(mut def: FunDef) -> FunDef {
    trace!("About to update: {}", def.name);
    def.body = simplify_st(def.body);
    def
}

pub fn simplify(defs: FunDefs) -> FunDefs {
    FunDefs::from_iter(defs.into_iter().map(|def| simplify_def(def)))
}
