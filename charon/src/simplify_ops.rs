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
    new_sequence, Assert, CtxNames, FunDecls, GlobalDecls, RawStatement, Statement, Switch, Var,
};
use crate::llbc_ast_utils::{MutAstVisitor, SharedAstVisitor};
use crate::meta::combine_meta;
use crate::types::*;
use crate::ullbc_ast::{iter_function_bodies, iter_global_bodies};
use crate::values::*;
use macros::{EnumAsGetters, EnumIsA};
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

/// Return true if the unary operation has a precondition (negating a number
/// won't lead to an overflow, for instance).
fn unop_requires_assert_before(unop: UnOp) -> bool {
    match unop {
        UnOp::Not => false,
        UnOp::Neg => true,
        UnOp::Cast(_, _) => {
            // This case is peculiar, because rustc doesn't insert assertions
            // while it can actually fail. TODO: actually, sure about that?
            false
        }
    }
}

fn unop_can_fail(unop: UnOp) -> bool {
    unop_requires_assert_before(unop)
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
                    assert!(true || release);
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
            assert!(true || !release || (value.is_int() && !value.is_min()));
            false
        }
        _ => {
            assert!(true || release);
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
                    assert!(true || release);
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
            assert!(true || release);
            false
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

/// Attempt to simplify a sequence of statements
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
        // Simplify checked binops (division, modulo)
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
            new_sequence(simpl_st, st4)
        }
        Option::None => simpl_st,
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
                    if binop_requires_assert_before(*binop) {
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

/// A pass dedicated to the simplification of binary operators which require
/// dynamic checks.
///
/// There are two kinds of such operators:
/// - the operators which require an assert *afterwards* (typically, addition:
///   we check that no over/under-flow occured).
///
///   They appear in MIR as:
///   ```
///     tmp := e1 <OP> e2
///     ...
///     assert (move tmp.0 == false)
///     ...
///     dst := move tmp.0
///   ```
///
///   We rewrite these as:
///   ```
///     tmp1 := e1 <OP> e2
///     ...
///     nop
///     ...
///     dst := move tmp1
///   ```
///
/// - the operators which require an assert *before* (typically, division: we
///   check that the divisor is not equal to zero before doing the operation).
///
///   They appear in MIR as:
///   ```
///     tmp := (copy divisor) == 0 // The divisor can be a constant
///     ...
///     assert (move tmp == false)
///     ...
///     dst := move dividend / divisor
///   ```
///   We rewrite these as:
///   ```
///     nop
///     ...
///     nop
///     ...
///     dst := move divident / divisor
///   ```
/// Later phases are concerned with further eliminating the nops and `tmp1`,
/// if possible.
///
/// Also, some of the checks may be present only in debug mode.

/// State to record if we eliminated binop operations which require to
/// check the result afterwards.
#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug, EnumAsGetters, EnumIsA)]
enum BinOpThenCheckState {
    /// We found a use of a binary operation.
    /// We store the fresh variable with which we will replace the current
    /// temporary variable.
    Defined(VarId::Id),
    FoundAssert(VarId::Id),
    FoundMove,
}

#[derive(Debug)]
struct SimplifyBinOpsThenCheck {
    tmp_vars: im::HashMap<VarId::Id, BinOpThenCheckState>,
    locals: VarId::Vector<Var>,
    /// Whenever we spawn a visitor in a branching, we insert it here.
    /// We merge them all upon calling [merge].
    spawned: Vec<Self>,
}

impl SimplifyBinOpsThenCheck {
    /// Given a temporary variable `v` of type (SCALAR, bool), return a fresh
    /// temporary variable `v'` of type `SCALAR` (that we also add to the locals).
    fn fresh_tmp_var_mapping(&mut self, v: VarId::Id) -> VarId::Id {
        // Lookup the variable
        let var = self.locals.get(v).unwrap();

        // Check its type
        let (tid, _, tys) = var.ty.as_adt();
        assert!(tid.is_tuple());
        assert!(tys.len() == 2);
        assert!(tys[1] == Ty::Bool);
        let scalar_ty = tys[0].clone();
        assert!(scalar_ty.is_integer());

        // Generate a fresh variable
        let n_vid = VarId::Id::new(self.locals.len());
        let n_var = Var {
            index: n_vid,
            name: None,
            ty: scalar_ty,
        };

        // Add to the locals
        self.locals.push_back(n_var);

        // Return
        n_vid
    }
}

impl MutExprVisitor for SimplifyBinOpsThenCheck {
    fn visit_var_id(&mut self, vid: &mut VarId::Id) {
        // Sanity check: the temporary variables are not used where they shouldn't
        assert!(self.tmp_vars.get(vid).is_none());
    }
}

impl MutAstVisitor for SimplifyBinOpsThenCheck {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        // Create a new visitor from self and push it at the end of the spawned visitors
        let mut nv = SimplifyBinOpsThenCheck {
            tmp_vars: self.tmp_vars.clone(),
            locals: self.locals.clone(),
            spawned: Vec::new(),
        };
        visitor(&mut nv);
        self.locals = nv.locals.clone();
        self.spawned.push(nv);
    }

    fn merge(&mut self) {
        // Replace the spawned iterators with an empty vector
        let mut spawned = std::mem::replace(&mut self.spawned, Vec::new());

        // There should be at least one spawned visitor
        let mut ntmp_vars = im::HashMap::new();

        // When merging merge the maps from variable id to state and while doing
        // so we check that all the states go to the `FoundMove` state (i.e.,
        // there is no pending simplification).
        //
        // This implies that no simplifiable operation is spread accross a
        // branching (i.e., some of the statements are before the branching
        // and some of the operations are after/inside the branches).
        for v in spawned {
            // Make a union of the two maps
            for (vid, nst) in v.tmp_vars.into_iter() {
                assert!(nst.is_found_move());
                let _ = ntmp_vars.insert(vid, nst);
            }
        }

        // Simply replace self with the new visitors
        self.tmp_vars = ntmp_vars;
    }

    fn visit_raw_statement(&mut self, s: &mut RawStatement) {
        // TODO: I think we should check that if we saw e1 <OP> e2 at some point,
        // we *do* find the corresponding assert and move (we need to check for
        // terminal nodes - and have to pay attention to branchings: we can
        // discuss that).
        match s {
            // 1. Find a statement of the form tmp := <op1> <bop> <op2>
            RawStatement::Assign(p, Rvalue::BinaryOp(bop, _, _))
                if binop_requires_assert_after(*bop) =>
            {
                assert!(p.projection.is_empty());

                // Replace the temporary variable
                let tmp = p.var_id;
                let ntmp = self.fresh_tmp_var_mapping(tmp);
                p.var_id = ntmp;

                // Initial state: we have seen the initial definition of the variable.
                assert!(self
                    .tmp_vars
                    .insert(tmp, BinOpThenCheckState::Defined(ntmp))
                    .is_none());
            }

            // 2. Catch assert (move tmp.1 == false)
            RawStatement::Assert(Assert {
                cond:
                    Operand::Move(Place {
                        var_id: v,
                        projection: p,
                    }),
                expected: false,
            }) => {
                if let Some(tmp_st) = self.tmp_vars.get(v) {
                    let tmp_st = *tmp_st;
                    let v = *v;
                    assert!(tmp_st.is_defined());
                    assert!(p.len() == 1);
                    assert!(p[0].as_field() == (&FieldProjKind::Tuple(2), &FieldId::Id::new(1)));

                    // Replace the statement
                    *s = RawStatement::Nop;

                    // Move to the next state: we have eliminated the assert, but still
                    // have to find the actual use.
                    let nst = BinOpThenCheckState::FoundAssert(*tmp_st.as_defined());
                    let _ = self.tmp_vars.insert(v, nst);
                } else {
                    self.default_visit_raw_statement(s)
                }
            }

            // 3. Catch dst := tmp.0
            RawStatement::Assign(
                _,
                Rvalue::Use(Operand::Move(Place {
                    var_id: v,
                    projection: p,
                })),
            ) => {
                if let Some(tmp_st) = self.tmp_vars.get(v) {
                    let tmp_st = *tmp_st;
                    let nvid = *tmp_st.as_found_assert();
                    assert!(p.len() == 1);
                    assert!(
                        p[0] == ProjectionElem::Field(FieldProjKind::Tuple(2), FieldId::Id::new(0))
                    );

                    // Replace the rvalue
                    let old_vid = *v;
                    *p = im::vector![];
                    *v = nvid;

                    // Final state: we have found and eliminated the use.
                    let _ = self
                        .tmp_vars
                        .insert(old_vid, BinOpThenCheckState::FoundMove);
                } else {
                    self.default_visit_raw_statement(s);
                }
            }

            _ => {
                self.default_visit_raw_statement(s);
            }
        }
    }
}

struct RemoveNops {}

impl MutExprVisitor for RemoveNops {}

impl MutAstVisitor for RemoveNops {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}

    fn visit_statement(&mut self, s: &mut Statement) {
        match &s.content {
            RawStatement::Sequence(s1, _) => {
                if s1.content.is_nop() {
                    take(s, |s| {
                        let (s1, s2) = s.content.to_sequence();
                        Statement {
                            content: s2.content,
                            meta: combine_meta(&s1.meta, &s2.meta),
                        }
                    })
                } else {
                    self.default_visit_raw_statement(&mut s.content)
                }
            }
            _ => self.default_visit_raw_statement(&mut s.content),
        }
    }
}

fn remove_nops(s: &mut Statement) {
    let mut v = RemoveNops {};
    v.visit_statement(s);
}

#[derive(Debug, Clone)]
pub(crate) struct ComputeUsedLocals {
    vars: im::HashMap<VarId::Id, usize>,
}

impl ComputeUsedLocals {
    fn new() -> Self {
        ComputeUsedLocals {
            vars: im::HashMap::new(),
        }
    }

    pub(crate) fn compute_in_statement(st: &Statement) -> im::HashMap<VarId::Id, usize> {
        let mut visitor = Self::new();
        visitor.visit_statement(st);
        visitor.vars
    }

    pub(crate) fn compute_in_operands(ops: &[Operand]) -> im::HashMap<VarId::Id, usize> {
        let mut visitor = Self::new();
        ops.iter().for_each(|op| visitor.visit_operand(op));
        visitor.vars
    }

    pub(crate) fn compute_used_set_in_operands(ops: &[Operand]) -> im::HashSet<VarId::Id> {
        im::HashSet::from_iter(Self::compute_in_operands(ops).into_iter().map(|(id, _)| id))
    }
}

impl SharedExprVisitor for ComputeUsedLocals {
    fn visit_var_id(&mut self, vid: &VarId::Id) {
        match self.vars.get_mut(vid) {
            Option::None => {
                let _ = self.vars.insert(*vid, 1);
            }
            Option::Some(cnt) => *cnt += 1,
        }
    }
}

impl SharedAstVisitor for ComputeUsedLocals {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}
}

/// `fmt_ctx` is used for pretty-printing purposes.
pub fn simplify(
    release: bool,
    fmt_ctx: &CtxNames<'_>,
    funs: &mut FunDecls,
    globals: &mut GlobalDecls,
) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to simplify operands in decl: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );

        // Apply the first simplification pass
        take(&mut b.body, |b| simplify_st(release, b));

        trace!(
            "# After first simplification pass of: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );

        if !release {
            // New series of passes implemented using the visitor.
            // First, eliminate binary operations.
            let mut s = SimplifyBinOpsThenCheck {
                tmp_vars: im::HashMap::new(),
                spawned: Vec::new(),
                locals: b.locals.clone(),
            };
            s.visit_statement(&mut b.body);
            b.locals = s.locals;

            trace!(
                "# After 2nd simplification pass of: {name}:\n{}\n\nstate:\n{:?}",
                b.fmt_with_ctx_names(fmt_ctx),
                &s.tmp_vars
            );

            // Sanity check: we performed all the required simplifications
            assert!(s.tmp_vars.iter().all(|(_, s)| s.is_found_move()));

            // Reconstruct the linked list of statements, skipping Nops
            remove_nops(&mut b.body);
        }

        trace!(
            "# After simplification of: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
    }
}
