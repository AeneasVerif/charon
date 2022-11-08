//! In MIR, many binops are desugared into:
//! * for division/modulo: a test that the divider is non zero (making the code
//!   panics if the divider is zero), then the division itself
//! * an operation, followed by a test: typically an addition followed by a check
//!   for overflow
//! This is a bit too low-level for us: we only want to have the binop (which will
//! have a precondition in our theorem prover, or will be monadic...). We thus want
//! to remove those unnecessary checks.
//!
//! Rem.: when compiling a Rust program in debug mode, Rustc introduces dynamic
//! checks everywhere. When compiling in release mode, it seems it only introduces
//! checks for division by zero.
//!
//! TODO: use [crate::llbc_ast_utils::transform_statements]

use take_mut::take;

use crate::expressions::*;
use crate::llbc_ast::{
    new_sequence, Assert, CtxNames, FunDecls, GlobalDecls, RawStatement, Statement, Switch,
};
use crate::meta::combine_meta;
use crate::types::*;
use crate::ullbc_ast::{iter_function_bodies, iter_global_bodies};
use crate::values::*;
use std::iter::FromIterator;

/// Small utility: assert that a boolean is true, or return false
macro_rules! assert_or_return {
    ($cond:expr $(,)?) => {{
        if !$cond {
            return false;
        }
    }};
    ($cond:expr, $($arg:tt)+) => {{
        if !$cond {
            trace!("assert_or_return failed: {}", $arg);
            return false;
        }
    }};
}

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

/// Return true if the binary operation might fail and thus requires its result
/// to be checked (overflows, for instance).
fn binop_requires_assert_after(binop: BinOp) -> bool {
    match binop {
        BinOp::BitXor
        | BinOp::BitAnd
        | BinOp::BitOr
        | BinOp::Eq
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Ne
        | BinOp::Ge
        | BinOp::Gt
        | BinOp::Div
        | BinOp::Rem => false,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Shl | BinOp::Shr => true,
    }
}

/// Return true if the unary operation has a precondition (negating the number
/// won't lead to an overflow, for instance).
fn unop_requires_assert_before(unop: UnOp) -> bool {
    match unop {
        UnOp::Not => false,
        UnOp::Neg => true,
        UnOp::Cast(_, _) => {
            // This case is peculiar, because rustc doesn't insert assertions
            // while it can actually fail
            false
        }
    }
}

fn unop_can_fail(unop: UnOp) -> bool {
    match unop {
        UnOp::Not => false,
        UnOp::Neg => true,
        UnOp::Cast(_, _) => {
            // See [unop_requires_assert_before]
            false
        }
    }
}

/// Return true if the binary operation has a precondition (divisor is non zero
/// for instance) and must thus be preceded by an assertion.
fn binop_requires_assert_before(binop: BinOp) -> bool {
    match binop {
        BinOp::BitXor
        | BinOp::BitAnd
        | BinOp::BitOr
        | BinOp::Eq
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Ne
        | BinOp::Ge
        | BinOp::Gt
        | BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::Shl
        | BinOp::Shr => false,
        BinOp::Div | BinOp::Rem => true,
    }
}

fn binop_can_fail(binop: BinOp) -> bool {
    binop_requires_assert_after(binop) || binop_requires_assert_before(binop)
}

/// Check if this is a group of statements of the form: "check that we can do
/// a unary operation, then do this operation (ex.: check that negating a number
/// won't lead to an overflow)", unless we compile for release mode.
fn check_if_assert_then_unop(
    release: bool,
    st1: &Statement,
    st2: &Statement,
    st3: &Statement,
) -> bool {
    match &st3.content {
        RawStatement::Assign(_, Rvalue::UnaryOp(unop, _)) => {
            if unop_requires_assert_before(*unop) {
                // We found a unary op with a precondition
                //
                // This group of statements should exactly match the following pattern:
                //   ```
                //   tmp := copy x == const (MIN ...); // `copy x` can be a constant
                //   assert(tmp == false);
                //   dest := -(move x); // `move x` can be a constant
                //   ...
                //   ```
                // If it is note the case, we can't collapse...
                check_if_simplifiable_assert_then_unop(release, st1, st2, st3)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Make sure the statements match the following pattern, unless we compile
/// for release:
///   ```text
///   tmp := copy x == const (MIN ...); // `copy x` can be a constant
///   assert(tmp == false);
///   dest := -(move x); // `move x` can be a constant
///   ...
///   ```
/// Or that there is no assert but the value is a constant which will not
/// lead to saturation.
fn check_if_simplifiable_assert_then_unop(
    release: bool,
    st1: &Statement,
    st2: &Statement,
    st3: &Statement,
) -> bool {
    match (&st1.content, &st2.content, &st3.content) {
        (
            RawStatement::Assign(
                eq_dest,
                Rvalue::BinaryOp(
                    BinOp::Eq,
                    op,
                    Operand::Const(
                        _,
                        OperandConstantValue::PrimitiveValue(PrimitiveValue::Scalar(saturated)),
                    ),
                ),
            ),
            RawStatement::Assert(Assert {
                cond: Operand::Move(cond_op),
                expected,
            }),
            RawStatement::Assign(_mp, Rvalue::UnaryOp(unop, op1)),
        ) => {
            // Case 1: pattern with assertion
            assert_or_return!(*unop == UnOp::Neg);
            assert_or_return!(!(*expected));

            assert_or_return!(eq_dest == cond_op);

            // Check the two operands:
            // - either they are (copy, move)
            // - or they are the same constant
            match (op, op1) {
                (Operand::Copy(p), Operand::Move(p1)) => assert!(p == p1),
                (Operand::Const(_, cv), Operand::Const(_, cv1)) => assert!(cv == cv1),
                _ => {
                    assert!(release);
                    return false;
                }
            }

            assert_or_return!(saturated.is_int() && saturated.is_min());
            true
        }
        (
            _,
            _,
            RawStatement::Assign(
                _mp,
                Rvalue::UnaryOp(
                    unop,
                    Operand::Const(
                        _,
                        OperandConstantValue::PrimitiveValue(PrimitiveValue::Scalar(value)),
                    ),
                ),
            ),
        ) => {
            assert!(*unop == UnOp::Neg);
            // Case 2: no assertion to check that there will not be an overflow:
            // - either we are in release mode
            // - or the value must be a constant which will not lead to an overflow.
            assert!(!release || (value.is_int() && !value.is_min()));
            false
        }
        _ => {
            assert!(release);
            false
        }
    }
}

/// Simplify patterns of the form:
///   ```text
///   tmp := copy x == const (MIN ...); // `copy x` can be a constant
///   assert(tmp == false);
///   dest := -(move x); // `move x` can be a constant
///   ...
///   ```
/// to:
///   ```text
///   dest := -(move x); // `move x` can be a constant
///   ...
///   ```
fn simplify_assert_then_unop(_st1: Statement, _st2: Statement, st3: Statement) -> Statement {
    st3
}

/// Check if this is a group of statements of the following form, unless we
/// compile for release:
/// - do an operation,
/// - check it succeeded (didn't overflow, etc.)
/// - retrieve the value
///
/// Check if this is a group of statements which should be collapsed to a
/// single checked binop.
/// Simply check if the first statements is a checked binop.
fn check_if_binop_then_assert(
    release: bool,
    st1: &Statement,
    st2: &Statement,
    st3: &Statement,
) -> bool {
    match &st1.content {
        RawStatement::Assign(_, Rvalue::BinaryOp(binop, _, _)) => {
            if binop_requires_assert_after(*binop) {
                // We found a checked binary op.
                //
                // This group of statements should exactly match the following pattern:
                //   ```
                //   tmp := copy x + copy y; // Possibly a different binop
                //   assert(move (tmp.1) == false);
                //   dest := move (tmp.0);
                //   ...
                //   ```
                // If it is note the case, we can't collapse...
                check_if_simplifiable_binop_then_assert(release, st1, st2, st3)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Make sure the statements match the following pattern, unless we compile
/// for release:
///   ```text
///   tmp := op1 + op2; // Possibly a different binop
///   assert(move (tmp.1) == false);
///   dest := move (tmp.0);
///   ...
///   ```
fn check_if_simplifiable_binop_then_assert(
    release: bool,
    st1: &Statement,
    st2: &Statement,
    st3: &Statement,
) -> bool {
    match (&st1.content, &st2.content, &st3.content) {
        (
            RawStatement::Assign(bp, Rvalue::BinaryOp(binop, _op1, _op2)),
            RawStatement::Assert(Assert {
                cond: Operand::Move(cond_op),
                expected,
            }),
            RawStatement::Assign(_mp, Rvalue::Use(Operand::Move(mr))),
        ) => {
            assert_or_return!(binop_requires_assert_after(*binop));
            assert_or_return!(!(*expected));

            // We must have:
            // cond_op == bp.1
            // mr == bp.0
            let check1 = check_places_similar_but_last_proj_elem(
                bp,
                &ProjectionElem::Field(FieldProjKind::Tuple(2), FieldId::Id::new(1)),
                cond_op,
            );
            assert_or_return!(check1);

            let check2 = check_places_similar_but_last_proj_elem(
                bp,
                &ProjectionElem::Field(FieldProjKind::Tuple(2), FieldId::Id::new(0)),
                mr,
            );
            assert_or_return!(check2);
            true
        }
        _ => {
            assert!(release);
            false
        }
    }
}

/// Simplify patterns of the following form, if we are in release mode:
///   ```text
///   tmp := op1 + op2; // Possibly a different binop
///   assert(move (tmp.1) == false);
///   dest := move (tmp.0);
///   ...
///   ```
/// to:
///   ```text
///   tmp := copy x + copy y; // Possibly a different binop
///   ...
///   ```
/// Note that the type of the binop changes in the two situations (in the
/// translation, before the transformation `+` returns a pair (bool, int),
/// after it has a monadic type).
fn simplify_binop_then_assert(st1: Statement, st2: Statement, st3: Statement) -> Statement {
    match (st1.content, st2.content, st3.content) {
        (RawStatement::Assign(_, binop), RawStatement::Assert(_), RawStatement::Assign(mp, _)) => {
            let meta = combine_meta(&st1.meta, &combine_meta(&st2.meta, &st3.meta));
            return Statement::new(meta, RawStatement::Assign(mp, binop));
        }
        _ => {
            unreachable!();
        }
    }
}

/// Check if this is a group of statements of the form: "check that we can do
/// an binary operation, then do this operation (ex.: check that a divisor is
/// non zero before doing a division, panic otherwise)"
fn check_if_assert_then_binop(
    release: bool,
    st1: &Statement,
    st2: &Statement,
    st3: &Statement,
) -> bool {
    match &st3.content {
        RawStatement::Assign(_, Rvalue::BinaryOp(binop, _, _)) => {
            if binop_requires_assert_before(*binop) {
                // We found an unchecked binop which should be simplified (division
                // or remainder computation).
                //
                // There are two situations:
                // - if the divisor is a non-zero constant, rust may not insert
                //   an assertion (because it can statically check it)
                // - otherwise, the group of statements must match the following
                //   pattern exactly:
                //   ```
                //   tmp := (copy divisor) == 0;
                //   assert((move tmp) == false);
                //   dest := move dividend / move divisor; // Can also be a `%`
                //   ...
                //   ```
                //
                //   Or this pattern:
                //   ```
                //   tmp := (constant_divisor) == 0;
                //   assert((move tmp) == false);
                //   dest := move dividend / constant_divisor; // Can also be a `%`
                //   ...
                //   ```
                check_if_simplifiable_assert_then_binop(release, st1, st2, st3)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Make sure the statements match the following pattern:
///   ```text
///   tmp := (copy divisor) == 0;
///   assert((move tmp) == false);
///   dest := move dividend / move divisor; // Can also be a `%`
///   ...
///   ```
/// Or that there is no assert but the divisor is a non-zero constant.
fn check_if_simplifiable_assert_then_binop(
    release: bool,
    st1: &Statement,
    st2: &Statement,
    st3: &Statement,
) -> bool {
    match (&st1.content, &st2.content, &st3.content) {
        (
            RawStatement::Assign(
                eq_dest,
                Rvalue::BinaryOp(
                    BinOp::Eq,
                    Operand::Copy(eq_op1),
                    Operand::Const(
                        _,
                        OperandConstantValue::PrimitiveValue(PrimitiveValue::Scalar(zero)),
                    ),
                ),
            ),
            RawStatement::Assert(Assert {
                cond: Operand::Move(cond_op),
                expected,
            }),
            RawStatement::Assign(_mp, Rvalue::BinaryOp(binop, _dividend, Operand::Move(divisor))),
        ) => {
            // Case 1: pattern with copy/move and assertion
            assert_or_return!(binop_requires_assert_before(*binop));
            assert_or_return!(!(*expected));
            assert_or_return!(eq_op1 == divisor);
            assert_or_return!(eq_dest == cond_op);
            if zero.is_int() {
                assert_or_return!(zero.as_int().unwrap() == 0);
            } else {
                assert_or_return!(zero.as_uint().unwrap() == 0);
            }
            true
        }
        (
            RawStatement::Assign(
                eq_dest,
                Rvalue::BinaryOp(
                    BinOp::Eq,
                    divisor,
                    Operand::Const(
                        _,
                        OperandConstantValue::PrimitiveValue(PrimitiveValue::Scalar(zero)),
                    ),
                ),
            ),
            RawStatement::Assert(Assert {
                cond: Operand::Move(cond_op),
                expected,
            }),
            RawStatement::Assign(_mp, Rvalue::BinaryOp(binop, _dividend, divisor1)),
        ) => {
            // Case 2: pattern with constant divisor and assertion
            assert_or_return!(binop_requires_assert_before(*binop));
            assert_or_return!(!(*expected));
            assert_or_return!(divisor.is_const());
            match divisor {
                Operand::Const(
                    _,
                    OperandConstantValue::PrimitiveValue(PrimitiveValue::Scalar(_)),
                ) => (),
                _ => {
                    assert!(release);
                    return false;
                }
            }
            assert_or_return!(divisor1 == divisor);
            assert_or_return!(eq_dest == cond_op);
            // Check that the zero is zero
            if zero.is_int() {
                assert_or_return!(zero.as_int().unwrap() == 0);
            } else {
                assert_or_return!(zero.as_uint().unwrap() == 0);
            }
            true
        }
        (_, _, RawStatement::Assign(_mp, Rvalue::BinaryOp(_, _, Operand::Const(_, divisor)))) => {
            // Case 3: no assertion to check the divisor != 0, the divisor must be a
            // non-zero constant integer
            let cv = divisor.as_primitive_value();
            let cv = cv.as_scalar();
            if cv.is_uint() {
                assert_or_return!(cv.as_uint().unwrap() != 0)
            } else {
                assert_or_return!(cv.as_int().unwrap() != 0)
            };
            false
        }
        _ => {
            assert!(release);
            return false;
        }
    }
}

/// Simplify patterns of the form:
///   ```text
///   tmp := (copy divisor) == 0;
///   assert((move tmp) == false);
///   dest := move dividend / move divisor; // Can also be a `%`
///   ...
///   ```
/// to:
///   ```text
///   dest := move dividend / move divisor; // Can also be a `%`
///   ...
///   ```
fn simplify_assert_then_binop(_st1: Statement, _st2: Statement, st3: Statement) -> Statement {
    st3
}

/// Attempt to simplify a sequence of statemnets
fn simplify_st_seq(
    release: bool,
    st1: Statement,
    st2: Statement,
    st3: Statement,
    st4: Option<Statement>,
) -> Statement {
    // Try to simplify
    let simpl_st = {
        // Simplify checked unops (negation)
        if check_if_assert_then_unop(release, &st1, &st2, &st3) {
            simplify_assert_then_unop(st1, st2, st3)
        }
        // Simplify checked binops
        else if check_if_binop_then_assert(release, &st1, &st2, &st3) {
            simplify_binop_then_assert(st1, st2, st3)
        }
        // Simplify unchecked binops (division, modulo)
        else if check_if_assert_then_binop(release, &st1, &st2, &st3) {
            simplify_assert_then_binop(st1, st2, st3)
        } else {
            // Not simplifyable
            let next_st = match st4 {
                Option::Some(st4) => new_sequence(st3, st4),
                Option::None => st3,
            };
            let next_st = new_sequence(st2, next_st);
            return new_sequence(simplify_st(release, st1), simplify_st(release, next_st));
        }
    };

    // Combine the simplified statements with the statement after, if there is
    match st4 {
        Option::Some(st4) => {
            let st4 = simplify_st(release, st4);
            return new_sequence(simpl_st, st4);
        }
        Option::None => return simpl_st,
    }
}

// TODO: don't consume `st`, use mutable borrows
fn simplify_st(release: bool, st: Statement) -> Statement {
    let content = match st.content {
        RawStatement::Assign(p, rv) => {
            // Check that we never failed to simplify a binop
            match &rv {
                Rvalue::BinaryOp(binop, _, divisor) => {
                    // If it is an unsimplified binop, it must be / or %
                    // and the divisor must be a non-zero constant integer,
                    // unless we compile for release
                    if binop_can_fail(*binop) {
                        match binop {
                            BinOp::Div | BinOp::Rem => {
                                let (_, cv) = divisor.as_const();
                                let cv = cv.as_primitive_value();
                                let cv = cv.as_scalar();
                                if cv.is_uint() {
                                    assert!(cv.as_uint().unwrap() != 0)
                                } else {
                                    assert!(cv.as_int().unwrap() != 0)
                                };
                            }
                            _ => {
                                assert!(release);
                            }
                        }
                    }
                }
                Rvalue::UnaryOp(unop, v) => {
                    // If it is an unsimplified unop which can fail, then:
                    // - it must be the negation, and
                    //   - either we compile for release
                    //   - or the value must be a constant integer which won't
                    //     lead to overflow.
                    if unop_can_fail(*unop) {
                        match unop {
                            UnOp::Neg => {
                                if release {
                                    // nothing to do
                                } else {
                                    let (_, cv) = v.as_const();
                                    let cv = cv.as_primitive_value();
                                    let cv = cv.as_scalar();
                                    assert!(cv.is_int());
                                    assert!(!cv.is_min());
                                }
                            }
                            _ => {
                                unreachable!();
                            }
                        }
                    }
                }
                _ => (),
            }
            RawStatement::Assign(p, rv)
        }
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
        RawStatement::Switch(switch) => {
            let switch = match switch {
                Switch::If(op, st1, st2) => Switch::If(
                    op,
                    Box::new(simplify_st(release, *st1)),
                    Box::new(simplify_st(release, *st2)),
                ),
                Switch::SwitchInt(op, int_ty, targets, mut otherwise) => {
                    let targets = Vec::from_iter(
                        targets
                            .into_iter()
                            .map(|(v, e)| (v, simplify_st(release, e))),
                    );
                    *otherwise = simplify_st(release, *otherwise);
                    Switch::SwitchInt(op, int_ty, targets, otherwise)
                }
                Switch::Match(_, _, _) => {
                    // We shouldn't get there: those are introduced later, in [remove_read_discriminant]
                    unreachable!();
                }
            };
            RawStatement::Switch(switch)
        }
        RawStatement::Loop(loop_body) => {
            RawStatement::Loop(Box::new(simplify_st(release, *loop_body)))
        }
        RawStatement::Sequence(st1, st2) => match st2.content {
            RawStatement::Sequence(st2, st3) => match st3.content {
                RawStatement::Sequence(st3, st4) => {
                    simplify_st_seq(release, *st1, *st2, *st3, Option::Some(*st4)).content
                }
                st3_raw => {
                    // Below: the fact that we moved the value is very annoying
                    simplify_st_seq(
                        release,
                        *st1,
                        *st2,
                        Statement::new(st3.meta, st3_raw),
                        Option::None,
                    )
                    .content
                }
            },
            st2_raw => RawStatement::Sequence(
                Box::new(simplify_st(release, *st1)),
                // Below: the fact that we moved the value is very annoying
                Box::new(simplify_st(release, Statement::new(st2.meta, st2_raw))),
            ),
        },
    };

    Statement::new(st.meta, content)
}

/// `fmt_ctx` is used for pretty-printing purposes.
pub fn simplify<'ctx>(
    release: bool,
    fmt_ctx: &CtxNames<'ctx>,
    funs: &mut FunDecls,
    globals: &mut GlobalDecls,
) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to simplify operands in decl: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
        take(&mut b.body, |b| simplify_st(release, b));
    }
}
