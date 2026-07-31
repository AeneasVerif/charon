//! # Micro-pass: remove the dynamic checks for array/slice bounds, overflow, and division by zero.
//! Note that from a semantic point of view, an out-of-bound access or a division by zero
//! must lead to a panic in Rust (which is why those checks are always present, even when
//! compiling for release). In our case, we take this into account in the semantics of our
//! array/slice manipulation and arithmetic functions, on the verification side.

use std::collections::HashSet;

use derive_generic_visitor::*;

use crate::ast::ullbc_ast_utils::StmtLoc;
use crate::ast::*;
use crate::ids::IndexVec;
use crate::transform::TransformCtx;
use crate::ullbc_ast::{BlockId, ExprBody, Statement, StatementKind};

use crate::transform::ctx::UllbcPass;

type LocalUses = IndexVec<BlockId, HashSet<LocalId>>;

/// Compute for each block the locals that are assumed to have been initialized/defined before entering it.
fn compute_uses(body: &ExprBody) -> LocalUses {
    #[derive(Visitor)]
    struct UsedLocalsVisitor<'a>(&'a mut HashSet<LocalId>);

    impl VisitBody for UsedLocalsVisitor<'_> {
        fn visit_place(&mut self, x: &Place) -> ::std::ops::ControlFlow<Self::Break> {
            if let Some(local_id) = x.as_local() {
                self.0.insert(local_id);
            }
            self.visit_inner(x)
        }
    }

    body.body.map_ref(|block| {
        let mut uses = HashSet::new();
        let mut visitor = UsedLocalsVisitor(&mut uses);

        // do a simple live variable analysis by walking the block backwards
        for statement in block.statements.iter().rev() {
            match &statement.kind {
                StatementKind::Assign(place, rval) => {
                    // We clear the assigned place, but it may be re-added
                    // if it's used in rval
                    if let Some(local_id) = place.as_local() {
                        visitor.0.remove(&local_id);
                    }
                    let _ = rval.drive_body(&mut visitor);
                }
                StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                    // A `StorageLive` re-sets the local to be uninitialised,
                    // so any usage after this point doesn't matter
                    // Similarly, a `StorageDead` means the local is de-initialised,
                    // so we can ignore any usage after this point
                    visitor.0.remove(local);
                }
                _ => {
                    let _ = statement.drive_body(&mut visitor);
                }
            }
        }

        uses
    })
}

/// Whether the value uses the given local in a place.
fn uses_local<T: BodyVisitable>(x: &T, local: LocalId) -> bool {
    struct FoundIt;
    struct UsesLocalVisitor(LocalId);

    impl Visitor for UsesLocalVisitor {
        type Break = FoundIt;
    }
    impl VisitBody for UsesLocalVisitor {
        fn visit_place(&mut self, x: &Place) -> ::std::ops::ControlFlow<Self::Break> {
            if let Some(local_id) = x.as_local()
                && local_id == self.0
            {
                return ControlFlow::Break(FoundIt);
            }
            self.visit_inner(x)
        }

        fn visit_ullbc_statement(
            &mut self,
            x: &ullbc_ast::Statement,
        ) -> ::std::ops::ControlFlow<Self::Break> {
            match x.kind {
                StatementKind::StorageDead(_) | StatementKind::StorageLive(_) => {
                    ControlFlow::Continue(())
                }
                _ => self.visit_inner(x),
            }
        }
    }

    x.drive_body(&mut UsesLocalVisitor(local)).is_break()
}

fn make_binop_overflow_panic<T: BodyVisitable>(
    x: &mut [T],
    matches: impl Fn(&BinOp, &Operand, &Operand) -> bool,
) -> bool {
    let mut found = false;
    for y in x.iter_mut() {
        y.dyn_visit_in_body_mut(|rv: &mut Rvalue| {
            if let Rvalue::BinaryOp(binop, op_l, op_r) = rv
                && matches(binop, op_l, op_r)
            {
                *binop = binop.with_overflow(OverflowMode::Panic);
                found = true;
            }
        });
    }
    found
}

fn make_unop_overflow_panic<T: BodyVisitable>(
    x: &mut [T],
    matches: impl Fn(&UnOp, &Operand) -> bool,
) -> bool {
    let mut found = false;
    for y in x.iter_mut() {
        y.dyn_visit_in_body_mut(|rv: &mut Rvalue| {
            if let Rvalue::UnaryOp(unop, op) = rv
                && matches(unop, op)
            {
                *unop = unop.with_overflow(OverflowMode::Panic);
                found = true;
            }
        });
    }
    found
}

/// Check if the two operands are equivalent: either they're the same constant, or they represent
/// the same place (regardless of whether the operand is a move or a copy)
fn equiv_op(op_l: &Operand, op_r: &Operand) -> bool {
    match (op_l, op_r) {
        (Operand::Copy(l) | Operand::Move(l), Operand::Copy(r) | Operand::Move(r)) => l == r,
        (Operand::Const(l), Operand::Const(r)) => l == r,
        _ => false,
    }
}

/// A shift overflow check whose shift operation is not in the same block: rustc evaluates the
/// shift operands (which is when it emits the overflow check) before computing the destination
/// place, so when that computation involves a function call (e.g. `out[i] = x >> y` through an
/// overloaded `IndexMut`), the check ends up separated from the shift by the call terminator.
/// See issue #1041. These asserts are only ever emitted by the compiler, so instead of following
/// the control flow we record the check and find the matching shift over the whole body in
/// [resolve_pending_shift_check].
struct PendingShiftCheck {
    /// The block containing the check.
    block: BlockId,
    /// The checked shift amount; used to find the shift.
    amount: Operand,
    /// The comparison result asserted by the check. Identifies the check's statements to remove.
    cond_local: LocalId,
    /// The `y as uN` cast temporary, when the amount is cast before the comparison; also removed.
    cast_local: Option<LocalId>,
}

/// Rustc inserts dynamic checks during MIR lowering. They all end in an `Assert` statement (and
/// this is the only use of this statement).
fn remove_dynamic_checks(
    _ctx: &mut TransformCtx,
    uses: &LocalUses,
    block_id: BlockId,
    locals: &mut Locals,
    statements: &mut [Statement],
    pending_shift_checks: &mut Vec<PendingShiftCheck>,
) {
    // Whether this local was used in another block
    let used_outside_block = |local: LocalId| {
        uses.iter_enumerated()
            .any(|(bid, used)| bid != block_id && used.contains(&local))
    };

    // We return the statements we want to keep, which must be a prefix of `block.statements`.
    let statements_to_keep = match statements {
        // Bounds checks for slices. They look like:
        //   l := use(copy a.metadata)
        //   b := copy x < copy l
        //   assert(move b == true)
        [
            Statement {
                kind: StatementKind::Assign(len, Rvalue::Use(Operand::Copy(len_op), _)),
                ..
            },
            Statement {
                kind:
                    StatementKind::Assign(
                        is_in_bounds,
                        Rvalue::BinaryOp(BinOp::Lt, _, Operand::Copy(lt_op2)),
                    ),
                ..
            },
            Statement {
                kind:
                    StatementKind::Assert {
                        assert:
                            Assert {
                                cond: Operand::Move(cond),
                                expected: true,
                                ..
                            },
                        ..
                    },
                ..
            },
            rest @ ..,
        ] if lt_op2 == len
            && cond == is_in_bounds
            && let Some((_, ProjectionElem::PtrMetadata)) = len_op.as_projection() =>
        {
            rest
        }
        // Sometimes that instead looks like:
        //   a := &raw const *z
        //   l := use(copy a.metadata)
        //   b := copy x < copy l
        //   assert(move b == true)
        [
            Statement {
                kind:
                    StatementKind::Assign(
                        reborrow,
                        Rvalue::RawPtr {
                            kind: RefKind::Shared,
                            ..
                        },
                    ),
                ..
            },
            Statement {
                kind: StatementKind::Assign(len, Rvalue::Use(Operand::Copy(len_op), _)),
                ..
            },
            Statement {
                kind:
                    StatementKind::Assign(
                        is_in_bounds,
                        Rvalue::BinaryOp(BinOp::Lt, _, Operand::Copy(lt_op2)),
                    ),
                ..
            },
            Statement {
                kind:
                    StatementKind::Assert {
                        assert:
                            Assert {
                                cond: Operand::Move(cond),
                                expected: true,
                                check_kind: Some(BuiltinAssertKind::BoundsCheck { .. }),
                            },
                        ..
                    },
                ..
            },
            rest @ ..,
        ] if lt_op2 == len
            && cond == is_in_bounds
            && let Some((slice_place, ProjectionElem::PtrMetadata)) = len_op.as_projection()
            && reborrow == slice_place =>
        {
            rest
        }

        // Zero checks for division and remainder. They look like:
        //   b := copy y == const 0
        //   assert(move b == false)
        //   ...
        //   res := x {/,%} move y;
        //   ... or ...
        //   b := const y == const 0
        //   assert(move b == false)
        //   ...
        //   res := x {/,%} const y;
        //
        // This also overlaps with overflow checks for negation, which looks like:
        //   is_min := x == INT::min
        //   assert(move is_min == false)
        //   ...
        //   res := -x;
        [
            Statement {
                kind:
                    StatementKind::Assign(
                        is_zero,
                        Rvalue::BinaryOp(BinOp::Eq, y_op, Operand::Const(_zero)),
                    ),
                ..
            },
            Statement {
                kind:
                    StatementKind::Assert {
                        assert:
                            Assert {
                                cond: Operand::Move(cond),
                                expected: false,
                                check_kind:
                                    Some(
                                        BuiltinAssertKind::DivisionByZero(_)
                                        | BuiltinAssertKind::RemainderByZero(_)
                                        | BuiltinAssertKind::OverflowNeg(_),
                                    ),
                            },
                        ..
                    },
                ..
            },
            rest @ ..,
        ] if cond == is_zero => {
            let found = make_binop_overflow_panic(rest, |bop, _, r| {
                matches!(bop, BinOp::Div(_) | BinOp::Rem(_)) && equiv_op(r, y_op)
            }) || make_unop_overflow_panic(rest, |unop, o| {
                matches!(unop, UnOp::Neg(_)) && equiv_op(o, y_op)
            });
            if found {
                rest
            } else {
                return;
            }
        }

        // Overflow checks for signed division and remainder. They look like:
        //   is_neg_1 := y == (-1)
        //   is_min := x == INT::min
        //   has_overflow := move (is_neg_1) & move (is_min)
        //   assert(move has_overflow == false)
        // Note here we don't need to update the operand to panic, as this was already done
        // by the previous pass for division by zero.
        [
            Statement {
                kind: StatementKind::Assign(is_neg_1, Rvalue::BinaryOp(BinOp::Eq, _y_op, _minus_1)),
                ..
            },
            Statement {
                kind: StatementKind::Assign(is_min, Rvalue::BinaryOp(BinOp::Eq, _x_op, _int_min)),
                ..
            },
            Statement {
                kind:
                    StatementKind::Assign(
                        has_overflow,
                        Rvalue::BinaryOp(
                            BinOp::BitAnd,
                            Operand::Move(and_op1),
                            Operand::Move(and_op2),
                        ),
                    ),
                ..
            },
            Statement {
                kind:
                    StatementKind::Assert {
                        assert:
                            Assert {
                                cond: Operand::Move(cond),
                                expected: false,
                                check_kind: Some(BuiltinAssertKind::Overflow(..)),
                            },
                        ..
                    },
                ..
            },
            rest @ ..,
        ] if and_op1 == is_neg_1 && and_op2 == is_min && cond == has_overflow => rest,

        // Overflow checks for right/left shift. They can look like:
        //   a := y as u32; // or another type
        //   b := move a < const 32; // or another constant
        //   assert(move b == true);
        //   ...
        //   res := x {<<,>>} y;
        [
            Statement {
                kind: StatementKind::Assign(cast, Rvalue::UnaryOp(UnOp::Cast(_), y_op)),
                ..
            },
            Statement {
                kind:
                    StatementKind::Assign(
                        has_overflow,
                        Rvalue::BinaryOp(BinOp::Lt, Operand::Move(lhs), Operand::Const(..)),
                    ),
                ..
            },
            Statement {
                kind:
                    StatementKind::Assert {
                        assert:
                            Assert {
                                cond: Operand::Move(cond),
                                expected: true,
                                check_kind: Some(BuiltinAssertKind::Overflow(..)),
                            },
                        ..
                    },
                ..
            },
            rest @ ..,
        ] if cond == has_overflow
            && lhs == cast
            && let Some(cast_local) = cast.as_local()
            && !rest.iter().any(|st| uses_local(st, cast_local)) =>
        {
            let found = make_binop_overflow_panic(rest, |bop, _, r| {
                matches!(bop, BinOp::Shl(_) | BinOp::Shr(_)) && equiv_op(r, y_op)
            });
            if found {
                rest
            } else {
                // The shift is not in this block; it may live in a later one (see
                // [PendingShiftCheck]). Record it and resolve it over the whole body afterwards.
                if let Some(cond_local) = has_overflow.as_local() {
                    pending_shift_checks.push(PendingShiftCheck {
                        block: block_id,
                        amount: y_op.clone(),
                        cond_local,
                        cast_local: Some(cast_local),
                    });
                }
                return;
            }
        }
        // or like:
        //   b := y < const 32; // or another constant
        //   assert(move b == true);
        //   ...
        //   res := x {<<,>>} y;
        //
        // this also overlaps with out of bounds checks for arrays, so we check for either;
        // these look like:
        //   b := copy y < const _
        //   assert(move b == true)
        //   ...
        //   res := a[y];
        [
            Statement {
                kind:
                    StatementKind::Assign(
                        has_overflow,
                        Rvalue::BinaryOp(BinOp::Lt, y_op, Operand::Const(..)),
                    ),
                ..
            },
            Statement {
                kind:
                    StatementKind::Assert {
                        assert:
                            Assert {
                                cond: Operand::Move(cond),
                                expected: true,
                                check_kind:
                                    check_kind @ Some(
                                        BuiltinAssertKind::Overflow(..)
                                        | BuiltinAssertKind::BoundsCheck { .. },
                                    ),
                            },
                        ..
                    },
                ..
            },
            rest @ ..,
        ] if cond == has_overflow => {
            // look for a shift operation
            let mut found = make_binop_overflow_panic(rest, |bop, _, r| {
                matches!(bop, BinOp::Shl(_) | BinOp::Shr(_)) && equiv_op(r, y_op)
            });
            if !found {
                // otherwise, look for an array access
                for stmt in rest.iter_mut() {
                    stmt.dyn_visit_in_body(|p: &Place| {
                        if let Some((_, ProjectionElem::Index { offset, .. })) = p.as_projection()
                            && equiv_op(offset, y_op)
                        {
                            found = true;
                        }
                    });
                }
            }

            if found {
                rest
            } else {
                // The shift may be in a later block (see [PendingShiftCheck]). This only applies
                // to overflow checks: a bounds check never guards a shift.
                if matches!(check_kind, Some(BuiltinAssertKind::Overflow(..)))
                    && let Some(cond_local) = has_overflow.as_local()
                {
                    pending_shift_checks.push(PendingShiftCheck {
                        block: block_id,
                        amount: y_op.clone(),
                        cond_local,
                        cast_local: None,
                    });
                }
                return;
            }
        }

        // Overflow checks for addition/subtraction/multiplication. They look like:
        // ```text
        //   r := x checked.+ y;
        //   assert(move r.1 == false);
        //   ...
        //   z := move r.0;
        // ```
        // We replace that with:
        // ```text
        // z := x panic.+ y;
        // ```
        //
        // But sometimes, because of constant promotion, we end up with a lone checked operation
        // without assert. In that case we replace it with its wrapping equivalent.
        [
            Statement {
                kind:
                    StatementKind::Assign(
                        tuple,
                        Rvalue::BinaryOp(
                            binop @ (BinOp::AddChecked | BinOp::SubChecked | BinOp::MulChecked),
                            _,
                            _,
                        ),
                    ),
                ..
            },
            rest @ ..,
        ] if let Some(tuple_local_id) = tuple.as_local()
            && !used_outside_block(tuple_local_id) =>
        {
            // Check if the result boolean is used in any other way than just getting the integer
            // result.
            let mut uses_of_tuple = 0;
            let mut uses_of_integer = 0;
            if *tuple == locals.return_place() {
                uses_of_tuple += 1; // The return place counts as a use.
            }
            for stmt in rest.iter_mut() {
                stmt.dyn_visit_in_body(|p: &Place| {
                    if p == tuple {
                        uses_of_tuple += 1;
                    }
                    if let Some((sub, ProjectionElem::Field(FieldProjKind::Tuple(..), fid))) =
                        p.as_projection()
                        && fid.index() == 0
                        && sub == tuple
                    {
                        uses_of_integer += 1;
                    }
                });
            }
            // Check if the operation is followed by an assert.
            let followed_by_assert = if let [
                Statement {
                    kind:
                        StatementKind::Assert {
                            assert:
                                Assert {
                                    cond: Operand::Move(assert_cond),
                                    expected: false,
                                    check_kind: Some(BuiltinAssertKind::Overflow(..)),
                                },
                            ..
                        },
                    ..
                },
                ..,
            ] = rest
                && let Some((sub, ProjectionElem::Field(FieldProjKind::Tuple(..), fid))) =
                    assert_cond.as_projection()
                && fid.index() == 1
                && sub == tuple
            {
                true
            } else {
                false
            };
            if uses_of_tuple != uses_of_integer && !followed_by_assert {
                // The tuple is used either directly or for the overflow check; we change nothing.
                return;
            }

            if followed_by_assert {
                // We have a compiler-emitted assert. We replace the operation with one that has
                // panic-on-overflow semantics.
                *binop = binop.with_overflow(OverflowMode::Panic);
                // The failure behavior is part of the binop now, so we remove the assert.
                rest[0].kind = StatementKind::Nop;
            } else {
                // The tuple is used exclusively to access the integer result, so we replace the
                // operation with wrapping semantics.
                *binop = binop.with_overflow(OverflowMode::Wrap);
            }
            // Fixup the local type.
            let result_local = &mut locals.locals[tuple_local_id];
            result_local.ty = result_local.ty.as_tuple().unwrap()[0].clone();
            // Fixup the place type.
            let new_result_place = locals.place_for_var(tuple_local_id);
            // Replace uses of `r.0` with `r`.
            for stmt in rest.iter_mut() {
                stmt.dyn_visit_in_body_mut(|p: &mut Place| {
                    if let Some((sub, ProjectionElem::Field(FieldProjKind::Tuple(..), fid))) =
                        p.as_projection()
                        && sub == tuple
                    {
                        assert_eq!(fid.index(), 0);
                        *p = new_result_place.clone()
                    }
                });
            }
            *tuple = new_result_place;
            return;
        }

        _ => return,
    };

    // Remove the statements we're not keeping.
    let keep_len = statements_to_keep.len();
    let removed_len = statements.len() - keep_len;
    for i in 0..removed_len {
        // If the statement we're removing assigns to a local that
        // is used elsewhere (in the leftover statements or in another block),
        // we don't remove it.
        if let StatementKind::Assign(place, _) = &statements[i].kind
            && let Some(local) = place.as_local()
            && let mut statements_to_keep = statements[removed_len..].as_ref().iter()
            && (used_outside_block(local) || statements_to_keep.any(|st| uses_local(st, local)))
        {
            continue;
        };
        statements[i].kind = StatementKind::Nop;
    }
}

/// Resolve a [PendingShiftCheck] whose shift landed in a different block. We remove the check and
/// compute the shift early, promoted to panic-on-overflow, into a fresh local placed where the
/// check used to be; the fresh local then carries the result to the original destination.
///
/// This is correct because rustc has already evaluated both shift operands by the time control
/// reaches the check: the only effects of the shift are that evaluation and the panic-on-overflow,
/// and the overflow check already performs both at that point. Storing the result in a fresh local
/// lets us keep the write to the (not-yet-computed) destination place at the original shift site.
fn resolve_pending_shift_check(body: &mut ExprBody, check: PendingShiftCheck) {
    let PendingShiftCheck {
        block,
        amount,
        cond_local,
        cast_local,
    } = check;

    // Locate the assert we will repurpose to hold the early, promoted shift. Pairing it with the
    // shift below (via `zip`) means we bail before mutating anything if either is unexpectedly
    // absent, so the shift is never rewired to a fresh local we never assigned.
    let assert_pos = body.body[block].statements.iter().position(|stmt| {
        matches!(
            &stmt.kind,
            StatementKind::Assert {
                assert: Assert {
                    cond: Operand::Move(cond),
                    ..
                },
                ..
            } if cond.as_local() == Some(cond_local)
        )
    });

    // rustc only emits these asserts for its own shifts, so we don't follow the control flow: we
    // look for the (still-wrapping) shift by its amount anywhere in the body.
    let Some(((shift_loc, dest, lhs, rhs, panic_binop, ty), assert_pos)) = body
        .body
        .iter_enumerated()
        .find_map(|(sb, block_data)| {
            block_data
                .statements
                .iter()
                .enumerate()
                .find_map(|(i, stmt)| {
                    if let StatementKind::Assign(dest, Rvalue::BinaryOp(binop, lhs, rhs)) =
                        &stmt.kind
                        && matches!(
                            binop,
                            BinOp::Shl(OverflowMode::Wrap) | BinOp::Shr(OverflowMode::Wrap)
                        )
                        && equiv_op(rhs, &amount)
                    {
                        Some((
                            StmtLoc::new(sb, i),
                            dest.clone(),
                            lhs.clone(),
                            rhs.clone(),
                            binop.with_overflow(OverflowMode::Panic),
                            dest.ty.clone(),
                        ))
                    } else {
                        None
                    }
                })
        })
        .zip(assert_pos)
    else {
        return;
    };

    // Every mutation below now happens together, so the fresh local is always assigned and used.
    let fresh = body.locals.new_var(None, ty);

    // Drop the check's comparison and optional cast; they are dead once the assert is gone.
    body.body[block].statements.iter_mut().for_each(|stmt| {
        let is_check_temp = if let StatementKind::Assign(place, _) = &stmt.kind {
            let local = place.as_local();
            local == Some(cond_local) || cast_local.is_some_and(|c| local == Some(c))
        } else {
            false
        };
        if is_check_temp {
            stmt.kind = StatementKind::Nop;
        }
    });

    // Compute the shift early, promoted to panic-on-overflow, where the check used to be.
    body[StmtLoc::new(block, assert_pos)].kind =
        StatementKind::Assign(fresh.clone(), Rvalue::BinaryOp(panic_binop, lhs, rhs));

    // Forward the result at the original shift site.
    body[shift_loc].kind =
        StatementKind::Assign(dest, Rvalue::Use(Operand::Move(fresh), WithRetag::No));
}

pub struct Transform;
impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.reconstruct_fallible_operations
    }

    fn transform_body(&self, ctx: &mut TransformCtx, b: &mut ExprBody) {
        let local_uses: LocalUses = compute_uses(b);
        let mut pending_shift_checks = Vec::new();
        b.transform_sequences_fwd(|id, locals, seq| {
            remove_dynamic_checks(ctx, &local_uses, id, locals, seq, &mut pending_shift_checks);
            Vec::new()
        });
        // Resolve the checks whose shift lives in a later block (see [PendingShiftCheck]).
        pending_shift_checks
            .into_iter()
            .for_each(|check| resolve_pending_shift_check(b, check));
    }
}
