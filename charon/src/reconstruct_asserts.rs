//! In the MIR AST, it seems `assert` are introduced to check preconditions
//! (for the binops for example). The `assert!` introduced by the user
//! introduce `if ... then { panic!(...) } else { ...}`.
//! This pass introduces `assert` instead in order to make the code shorter.

use crate::cfim_ast::*;
use hashlink::linked_hash_map::LinkedHashMap;
use std::iter::FromIterator;

fn exp_is_panic(exp: &Expression) -> bool {
    match exp {
        Expression::Statement(Statement::Panic) => true,
        _ => false,
    }
}

fn simplify_exp(exp: Expression) -> Expression {
    match exp {
        Expression::Statement(st) => Expression::Statement(st),
        Expression::Switch(op, targets) => {
            match targets {
                SwitchTargets::If(exp1, exp2) => {
                    let exp2 = Box::new(simplify_exp(*exp2));

                    // Check if the first expression is a panic: if yes, replace
                    // the if .. then ... else ... by an assertion.
                    if exp_is_panic(&exp1) {
                        let exp1 = Statement::Assert(Assert {
                            cond: op,
                            expected: false,
                        });
                        let exp1 = Box::new(Expression::Statement(exp1));

                        Expression::Sequence(exp1, exp2)
                    } else {
                        let targets = SwitchTargets::If(Box::new(simplify_exp(*exp1)), exp2);
                        Expression::Switch(op, targets)
                    }
                }
                SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                    let targets = LinkedHashMap::from_iter(
                        targets.into_iter().map(|(v, e)| (v, simplify_exp(e))),
                    );
                    let otherwise = simplify_exp(*otherwise);
                    let targets = SwitchTargets::SwitchInt(int_ty, targets, Box::new(otherwise));
                    Expression::Switch(op, targets)
                }
            }
        }
        Expression::Loop(loop_body) => Expression::Loop(Box::new(simplify_exp(*loop_body))),
        Expression::Sequence(exp1, exp2) => match *exp2 {
            Expression::Sequence(exp2, exp3) => {
                Expression::Sequence(Box::new(simplify_exp(*exp2)), Box::new(simplify_exp(*exp3)))
            }
            exp2 => {
                Expression::Sequence(Box::new(simplify_exp(*exp1)), Box::new(simplify_exp(exp2)))
            }
        },
    }
}
fn simplify_decl(mut decl: FunDecl) -> FunDecl {
    trace!("About to update: {}", decl.name);
    decl.body = simplify_exp(decl.body);
    decl
}

pub fn simplify(decls: FunDecls) -> FunDecls {
    FunDecls::from_iter(decls.into_iter().map(|decl| simplify_decl(decl)))
}
