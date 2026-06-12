//! # Micro-pass: reconstruct pointer null-checks.
//!
//! When rustc lowers a pointer null-check (e.g. `<*const T>::is_null`), it reinterprets the
//! pointer's bits as an integer and tests that integer against `0`. Depending on the MIR level, the
//! test takes one of two shapes:
//! ```text
//! // optimized MIR: the comparison is a `switch` terminator
//! _23 := transmute<*mut u8, usize>(copy raw_ptr_6);
//! switch copy _23 -> [0: bb20, otherwise: bb21]
//!
//! // built MIR: the comparison is a `== 0` / `!= 0` statement
//! _3 := transmute<*const u8, usize>(copy _2);
//! _0 := move _3 == const 0usize;
//! ```
//!
//! Some tools would like to avoid reasoning about the pointer-to-integer transmutation. Instead we
//! compare the pointer against the null pointer (a no-provenance pointer with address `0`), so
//! that the comparison stays in the pointer world:
//! ```text
//! _tmp := copy raw_ptr_6 != const (no-provenance 0);
//! _23 := cast<bool, usize>(move _tmp);
//! switch copy _23 -> [0: bb20, otherwise: bb21]
//! ```
//! The new value assigned to `_23` is `0` if and only if the pointer is null, exactly like the
//! transmuted address it replaces, so the null-check itself is left untouched. The only
//! information lost is the address of a non-null pointer (the value becomes `1`), which is sound
//! because that value feeds nothing but the null-check.
//!
//! The transformation is only fired when:
//! - we transmute a *sized* (thin) pointer to `usize`/`isize`;
//! - the result feeds either a switch with a single `0` case and an otherwise branch, or a
//!   `== 0` / `!= 0` comparison against the null address;
//! - the transmuted value is used nowhere else (necessary for soundness)

use derive_generic_visitor::Visitor;
use std::ops::ControlFlow::{self, Continue};

use crate::ids::IndexVec;
use crate::transform::TransformCtx;
use crate::transform::ctx::UllbcPass;
use crate::ullbc_ast::*;

/// Count how many times each local appears in the body, ignoring `StorageLive`/`StorageDead`
/// statements (which mention a local but don't actually use its value).
#[derive(Visitor)]
struct LocalUsageCounter {
    counts: IndexVec<LocalId, usize>,
}

impl VisitBody for LocalUsageCounter {
    fn enter_local_id(&mut self, lid: &LocalId) {
        self.counts[*lid] += 1;
    }
    fn visit_ullbc_statement(&mut self, st: &Statement) -> ControlFlow<Self::Break> {
        match &st.kind {
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => Continue(()),
            _ => self.visit_inner(st),
        }
    }
}

fn count_local_usages(b: &ExprBody) -> IndexVec<LocalId, usize> {
    let mut visitor = LocalUsageCounter {
        counts: b.locals.locals.map_ref(|_| 0),
    };
    let _ = b.body.drive_body(&mut visitor);
    visitor.counts
}

/// Whether `local`'s non-defining use is a pointer null-check, i.e. either:
/// - a `switch local -> [0: _, otherwise: _]` terminator (the shape rustc emits in *optimized*
///   MIR), or
/// - a `_ = (local == 0)` / `_ = (local != 0)` comparison statement (the shape rustc emits in
///   *built* MIR, where `<*const T>::is_null` is `transmute::<*T, usize>(p) == 0`).
///
/// The caller guarantees `local` is used exactly twice, so whichever use we find here is its unique
/// non-defining use.
fn feeds_null_check(block: &BlockData, local: LocalId) -> bool {
    // The result feeds a `switch [0, otherwise]` terminator.
    if let TerminatorKind::Switch {
        discr,
        targets: SwitchTargets::SwitchInt(_, cases, _),
    } = &block.terminator.kind
        && let [(case, _)] = cases.as_slice()
        && case.is_zero()
        && discr.as_local() == Some(local)
    {
        return true;
    }
    // The result feeds a `== 0` / `!= 0` comparison against the null address.
    block.statements.iter().any(|st| {
        matches!(
            &st.kind,
            StatementKind::Assign(_, Rvalue::BinaryOp(BinOp::Eq | BinOp::Ne, lhs, rhs))
                if (lhs.as_local() == Some(local) && rhs.is_zero_constant())
                    || (rhs.as_local() == Some(local) && lhs.is_zero_constant())
        )
    })
}

/// If `st` is a `transmute` of a sized (thin) pointer into a `usize`/`isize` whose result is used
/// exactly twice and whose unique other use is a null-check (a `switch [0, _]` or a `== 0` /
/// `!= 0` within `block`), return the assigned place, the pointer type, the target integer type
/// and the transmuted operand.
fn match_transmuted_null_check<'a>(
    ctx: &TransformCtx,
    usages: &IndexVec<LocalId, usize>,
    block: &'a BlockData,
    st: &'a Statement,
) -> Option<(&'a Place, &'a Ty, LiteralTy, &'a Operand)> {
    let StatementKind::Assign(
        place,
        Rvalue::UnaryOp(UnOp::Cast(CastKind::Transmute(src_ty, tgt_ty)), op),
    ) = &st.kind
    else {
        return None;
    };
    let result = place.as_local()?;
    let TyKind::Literal(
        tgt_lit_ty @ (LiteralTy::UInt(UIntTy::Usize) | LiteralTy::Int(IntTy::Isize)),
    ) = tgt_ty.kind()
    else {
        return None;
    };
    if usages[result] != 2 {
        return None;
    }
    let (TyKind::RawPtr(pointee, _) | TyKind::Ref(_, pointee, _)) = src_ty.kind() else {
        return None;
    };
    if !matches!(pointee.get_ptr_metadata(&ctx.translated), PtrMetadata::None) {
        return None;
    }
    if !feeds_null_check(block, result) {
        return None;
    }
    Some((place, src_ty, *tgt_lit_ty, op))
}

pub struct Transform;

impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.reconstruct_null_checks
    }

    fn transform_body(&self, ctx: &mut TransformCtx, b: &mut ExprBody) {
        let usages = count_local_usages(b);

        let locals = &mut b.locals;
        for block in b.body.iter_mut() {
            let mut idx = 0;
            while idx < block.statements.len() {
                let Some((dest, src_ty, tgt_lit_ty, operand)) =
                    match_transmuted_null_check(ctx, &usages, block, &block.statements[idx])
                        .map(|(place, ty, lit, op)| (place.clone(), ty.clone(), lit, op.clone()))
                else {
                    idx += 1;
                    continue;
                };
                let span = block.statements[idx].span;

                // `(p != null) as usize` is `0` exactly when `transmute::<_, usize>(p)` is, so the
                // downstream null-check is left untouched.
                let tmp = locals.new_var(None, Ty::mk_bool());
                let tmp_local = tmp.as_local().unwrap();
                let null_ptr = Operand::Const(Box::new(ConstantExpr {
                    kind: ConstantExprKind::PtrNoProvenance(0),
                    ty: src_ty,
                }));
                let is_not_null = Rvalue::BinaryOp(BinOp::Ne, operand, null_ptr);
                let cast = Rvalue::UnaryOp(
                    UnOp::Cast(CastKind::Scalar(LiteralTy::Bool, tgt_lit_ty)),
                    Operand::Move(tmp.clone()),
                );
                let new_statements = [
                    StatementKind::StorageLive(tmp_local),
                    StatementKind::Assign(tmp, is_not_null),
                    StatementKind::Assign(dest, cast),
                    StatementKind::StorageDead(tmp_local),
                ]
                .map(|kind| Statement::new(span, kind));
                let num_new = new_statements.len();
                block.statements.splice(idx..=idx, new_statements);
                idx += num_new;
            }
        }
    }
}
