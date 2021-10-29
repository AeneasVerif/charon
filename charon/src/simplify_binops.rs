//! In MIR, many binops are desugared into:
//! * for division/modulo: a test that the divider is non zero (making the code
//!   panics if the divider is zero), then the division itself
//! * an operation, followed by a test: typically an addition followed by a check
//!   for overflow
//! This is a bit too low-level for us: we only want to have the binop (which will
//! have a precondition in our theorem prover, or will be monadic...). We thus want
//! to remove those unnecessary checks.

use crate::cfim_ast::*;
use crate::expressions::*;
use crate::types::*;
use crate::values::*;
use hashlink::linked_hash_map::LinkedHashMap;
use std::iter::FromIterator;

/// Return true iff: `place ++ [pelem] == full_place`
fn check_places_similar_but_last_proj_elem(
    place: &Place,
    pelem: &ProjectionElem,
    full_place: &Place,
) -> bool {
    if place.var_id == full_place.var_id
        && place.projection.len() + 1 == full_place.projection.len()
    {
        for i in 0..place.projection.len() {
            if place.projection[i] != full_place.projection[i] {
                return false;
            }
        }

        return *pelem == full_place.projection[place.projection.len()];
    }
    return false;
}

/// Look for pattern of the form:
///   ```
///   var@5 := copy (var@3) + copy (var@4);
///   assert(move ((var@5).1) == false);
///   var@0 := move ((var@5).0);
///   ...
///   ```
fn check_if_simplifiable_checked_binop(
    exp1: &Expression,
    exp2: &Expression,
    exp3: &Expression,
) -> bool {
    match (exp1, exp2, exp3) {
        (
            Expression::Statement(Statement::Assign(
                bp,
                Rvalue::CheckedBinaryOp(_binop, _op1, _op2),
            )),
            Expression::Statement(Statement::Assert(Assert {
                cond: Operand::Move(cond_op),
                expected,
            })),
            Expression::Statement(Statement::Assign(_mp, Rvalue::Use(Operand::Move(mr)))),
        ) => {
            if *expected {
                return false;
            }

            // We must have:
            // cond_op == bp.1
            // mr == bp.0

            return check_places_similar_but_last_proj_elem(
                bp,
                &ProjectionElem::Field(FieldId::Id::new(1)),
                cond_op,
            ) && check_places_similar_but_last_proj_elem(
                bp,
                &ProjectionElem::Field(FieldId::Id::new(0)),
                mr,
            );
        }
        _ => {
            return false;
        }
    }
}

/// Simplify patterns of the form:
///   ```
///   var@5 := copy (var@3) + copy (var@4);
///   assert(move ((var@5).1) == false);
///   var@0 := move ((var@5).0);
///   ...
///   ```
/// to:
///   ```
///   var@0 := copy (var@3) + copy (var@4);
///   ...
///   ```
/// Note that the type of the binop changes in the two situations (in the
/// translation, before the transformation `+` returns a pair (bool, int),
/// after it has a monadic type).
fn simplify_checked_binop(exp1: Expression, exp2: Expression, exp3: Expression) -> Expression {
    match (exp1, exp2, exp3) {
        (
            Expression::Statement(Statement::Assign(_, binop)),
            Expression::Statement(Statement::Assert(_)),
            Expression::Statement(Statement::Assign(mp, _)),
        ) => {
            return Expression::Statement(Statement::Assign(mp, binop));
        }
        _ => {
            unreachable!();
        }
    }
}

/// Look for pattern of the form:
///   ```
///   var@5 := copy (var@4) == const (0 : u32);
///   assert(move (var@5) == false);
///   var@0 := move (var@3) / move (var@4);
///   ...
///   ```
fn check_if_simplifiable_unchecked_binop(
    exp1: &Expression,
    exp2: &Expression,
    exp3: &Expression,
) -> bool {
    match (exp1, exp2, exp3) {
        (
            Expression::Statement(Statement::Assign(
                eq_dest,
                Rvalue::BinaryOp(
                    BinOp::Eq,
                    Operand::Copy(eq_op1),
                    Operand::Constant(
                        _,
                        OperandConstantValue::ConstantValue(ConstantValue::Scalar(scalar_value)),
                    ),
                ),
            )),
            Expression::Statement(Statement::Assert(Assert {
                cond: Operand::Move(cond_op),
                expected,
            })),
            Expression::Statement(Statement::Assign(
                _mp,
                Rvalue::BinaryOp(binop, _dividend, Operand::Move(divisor)),
            )),
        ) => {
            if *binop != BinOp::Div && *binop != BinOp::Rem {
                return false;
            }

            if *expected {
                return false;
            }

            if eq_op1 != divisor || eq_dest != cond_op {
                return false;
            }
            if scalar_value.is_int() {
                return scalar_value.as_int().unwrap() == 0;
            } else {
                return scalar_value.as_uint().unwrap() == 0;
            }
        }
        _ => {
            return false;
        }
    }
}

/// Simplify patterns of the form:
///   ```
///   var@5 := copy (var@4) == const (0 : u32);
///   assert(move (var@5) == false);
///   var@0 := move (var@3) / move (var@4);
///   ...
///   ```
/// to:
///   ```
///   var@0 := move (var@3) / move (var@4);
///   ...
///   ```
fn simplify_unchecked_binop(_exp1: Expression, _exp2: Expression, exp3: Expression) -> Expression {
    exp3
}

/// Check if the statement is an assignment which uses a binop which can fail
/// (it is a checked binop, or a binop with a precondition like division)
fn statement_is_faillible_binop(st: &Statement) -> bool {
    match st {
        Statement::Assign(_, Rvalue::CheckedBinaryOp(_, _, _)) => true,
        Statement::Assign(_, Rvalue::BinaryOp(binop, _, _)) => match binop {
            BinOp::BitXor
            | BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::Eq
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Ne
            | BinOp::Ge
            | BinOp::Gt => false,
            BinOp::Div | BinOp::Rem => true,
        },
        _ => false,
    }
}

fn simplify_exp(exp: Expression) -> Expression {
    match exp {
        Expression::Statement(st) => {
            // Check that we never have to simplify a statement which should
            // have been simplified when seen in a statement sequence.
            assert!(!statement_is_faillible_binop(&st));
            Expression::Statement(st)
        }
        Expression::Switch(op, targets) => {
            let targets = match targets {
                SwitchTargets::If(exp1, exp2) => {
                    SwitchTargets::If(Box::new(simplify_exp(*exp1)), Box::new(simplify_exp(*exp2)))
                }
                SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                    let targets = LinkedHashMap::from_iter(
                        targets.into_iter().map(|(v, e)| (v, simplify_exp(e))),
                    );
                    let otherwise = simplify_exp(*otherwise);
                    SwitchTargets::SwitchInt(int_ty, targets, Box::new(otherwise))
                }
            };
            Expression::Switch(op, targets)
        }
        Expression::Loop(loop_body) => Expression::Loop(Box::new(simplify_exp(*loop_body))),
        Expression::Sequence(exp1, exp2) => match *exp2 {
            Expression::Sequence(exp2, exp3) => {
                match *exp3 {
                    Expression::Sequence(exp3, exp4) => {
                        // Simplify checked binops
                        if check_if_simplifiable_checked_binop(&exp1, &exp2, &exp3) {
                            let exp = simplify_checked_binop(*exp1, *exp2, *exp3);
                            let exp4 = simplify_exp(*exp4);
                            return Expression::Sequence(Box::new(exp), Box::new(exp4));
                        }

                        // Simplify unchecked binops (division, modulo)
                        // Pattern:
                        //   ```
                        //   var@5 := copy (var@4) == const (0 : u32);
                        //   assert(move (var@5) == false);
                        //   var@0 := move (var@3) / move (var@4);
                        //   ```
                        if check_if_simplifiable_unchecked_binop(&exp1, &exp2, &exp3) {
                            let exp = simplify_unchecked_binop(*exp1, *exp2, *exp3);
                            let exp4 = simplify_exp(*exp4);
                            Expression::Sequence(Box::new(exp), Box::new(exp4))
                        }
                        // Not simplifyable
                        else {
                            let exp2 = Expression::Sequence(
                                exp2,
                                Box::new(Expression::Sequence(exp3, exp4)),
                            );
                            Expression::Sequence(
                                Box::new(simplify_exp(*exp1)),
                                Box::new(simplify_exp(exp2)),
                            )
                        }
                    }
                    exp3 => Expression::Sequence(
                        Box::new(simplify_exp(*exp1)),
                        Box::new(simplify_exp(Expression::Sequence(exp2, Box::new(exp3)))),
                    ),
                }
            }
            exp2 => {
                Expression::Sequence(Box::new(simplify_exp(*exp1)), Box::new(simplify_exp(exp2)))
            }
        },
    }
}

fn simplify_decl(mut decl: FunDecl) -> FunDecl {
    trace!("About to simplify: {}", decl.name);
    decl.body = simplify_exp(decl.body);
    decl
}

pub fn simplify(decls: FunDecls) -> FunDecls {
    FunDecls::from_iter(decls.into_iter().map(|decl| simplify_decl(decl)))
}
