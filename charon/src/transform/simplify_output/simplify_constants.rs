//! The MIR constant expressions lead to a lot of duplication: there are
//! for instance constant ADTs which duplicate the "regular" aggregated
//! ADTs in the operands, constant references, etc. This reduces the number
//! of cases to handle and eases the function translation in Aeneas.
//!
//! This pass removes all those occurrences so that only the
//! `ConstantExpression::Literal`. It does so by introducing intermediate statements.
//!
//! A small remark about the intermediate statements we introduce for the globals:
//! we do so because, when evaluating the code in "concrete" mode, it allows to
//! handle the globals like function calls.

use itertools::Itertools;
use std::assert_matches::assert_matches;

use crate::transform::TransformCtx;
use crate::transform::ctx::{BodyTransformCtx, UllbcPass, UllbcStatementTransformCtx};
use crate::ullbc_ast::*;

/// If the constant value is a constant ADT, push `Assign::Aggregate` statements
/// to the vector of statements, that bind new variables to the ADT parts and
/// the variable assigned to the complete ADT.
///
/// Goes fom e.g. `f(T::A(x, y))` to `let a = T::A(x, y); f(a)`.
/// The function is recursively called on the aggregate fields (e.g. here x and y).
fn transform_constant_expr(
    ctx: &mut UllbcStatementTransformCtx<'_>,
    val: Box<ConstantExpr>,
) -> Operand {
    let rval = match val.kind {
        ConstantExprKind::Literal(_)
        | ConstantExprKind::Var(_)
        | ConstantExprKind::RawMemory(..)
        | ConstantExprKind::TraitConst(..)
        | ConstantExprKind::FnPtr(..)
        | ConstantExprKind::Opaque(_) => {
            // Nothing to do
            // TODO: for trait const: might come from a top-level impl, so we might
            // want to introduce an intermediate statement to be able to evaluate
            // it as a function call, like for globals.
            return Operand::Const(val);
        }
        // Here we use a copy, rather than a move -- moving a global would leave it uninitialized,
        // which would e.g. make the following code fail:
        //     const GLOBAL: usize = 0;
        //     let x = GLOBAL;
        //     let y = GLOBAL; // if moving, at this point GLOBAL would be uninitialized
        ConstantExprKind::Global(global_ref) => {
            return Operand::Copy(Place::new_global(global_ref, val.ty));
        }
        ConstantExprKind::PtrNoProvenance(ptr) => {
            let usize_ty = TyKind::Literal(LiteralTy::UInt(UIntTy::Usize)).into_ty();
            let ptr_usize = ConstantExprKind::Literal(Literal::Scalar(ScalarValue::Unsigned(
                UIntTy::Usize,
                ptr,
            )));
            let cast = UnOp::Cast(CastKind::RawPtr(usize_ty.clone(), val.ty.clone()));
            Rvalue::UnaryOp(
                cast,
                Operand::Const(Box::new(ConstantExpr {
                    kind: ptr_usize,
                    ty: usize_ty,
                })),
            )
        }
        ConstantExprKind::Ref(bval) => {
            let place = match bval.kind {
                ConstantExprKind::Global(global_ref) => Place::new_global(global_ref, bval.ty),
                _ => {
                    // Recurse on the borrowed value
                    let bval = transform_constant_expr(ctx, bval);

                    // Evaluate the referenced value
                    let bval_ty = bval.ty().clone();
                    ctx.rval_to_place(Rvalue::Use(bval), bval_ty)
                }
            };
            // Borrow the place.
            ctx.borrow(place, BorrowKind::Shared)
        }
        ConstantExprKind::Ptr(rk, bval) => {
            // As the value is originally an argument, it must be Sized, hence no metadata
            let place = match bval.kind {
                ConstantExprKind::Global(global_ref) => Place::new_global(global_ref, bval.ty),
                _ => {
                    // Recurse on the borrowed value
                    let bval = transform_constant_expr(ctx, bval);

                    // Evaluate the referenced value
                    let bval_ty = bval.ty().clone();
                    ctx.rval_to_place(Rvalue::Use(bval), bval_ty)
                }
            };
            // Borrow the value
            ctx.raw_borrow(place, rk)
        }
        ConstantExprKind::Adt(variant, fields) => {
            let fields = fields
                .into_iter()
                .map(|x| transform_constant_expr(ctx, Box::new(x)))
                .collect();

            // Build an `Aggregate` rvalue.
            let tref = val.ty.kind().as_adt().unwrap();
            let aggregate_kind = AggregateKind::Adt(tref.clone(), variant, None);
            Rvalue::Aggregate(aggregate_kind, fields)
        }
        ConstantExprKind::Array(fields) => {
            let fields = fields
                .into_iter()
                .map(|x| transform_constant_expr(ctx, Box::new(x)))
                .collect_vec();

            let len = ConstGeneric::Value(Literal::Scalar(ScalarValue::Unsigned(
                UIntTy::Usize,
                fields.len() as u128,
            )));
            let tref = val.ty.kind().as_adt().unwrap();
            assert_matches!(
                *tref.id.as_builtin().unwrap(),
                BuiltinTy::Array | BuiltinTy::Slice
            );
            let ty = tref.generics.types[0].clone();
            Rvalue::Aggregate(AggregateKind::Array(ty, len), fields)
        }
    };
    Operand::Move(ctx.rval_to_place(rval, val.ty))
}

fn transform_operand(ctx: &mut UllbcStatementTransformCtx<'_>, op: &mut Operand) {
    // Transform the constant operands (otherwise do nothing)
    take_mut::take(op, |op| {
        if let Operand::Const(val) = op {
            transform_constant_expr(ctx, val)
        } else {
            op
        }
    })
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_function(&self, ctx: &mut TransformCtx, fun_decl: &mut FunDecl) {
        if ctx.options.raw_consts {
            return;
        }
        fun_decl.transform_ullbc_operands(ctx, transform_operand);
        if let Some(body) = fun_decl.body.as_unstructured_mut() {
            for block in body.body.iter_mut() {
                // Simplify array with repeated constants into array repeats.
                block.dyn_visit_in_body_mut(|rvalue: &mut Rvalue| {
                    take_mut::take(rvalue, |rvalue| match rvalue {
                        Rvalue::Aggregate(AggregateKind::Array(ty, len), ref fields)
                            if fields.len() >= 2
                                && fields.iter().all(|x| x.is_const())
                                && let Ok(op) = fields.iter().dedup().exactly_one() =>
                        {
                            Rvalue::Repeat(op.clone(), ty.clone(), len)
                        }
                        _ => rvalue,
                    });
                });
            }
        }
    }
}
