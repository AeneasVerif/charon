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
use crate::ullbc_ast::*;

use crate::transform::ctx::UllbcPass;

/// If the constant value is a constant ADT, push `Assign::Aggregate` statements
/// to the vector of statements, that bind new variables to the ADT parts and
/// the variable assigned to the complete ADT.
///
/// Goes fom e.g. `f(T::A(x, y))` to `let a = T::A(x, y); f(a)`.
/// The function is recursively called on the aggregate fields (e.g. here x and y).
fn transform_constant_expr(
    span: &Span,
    val: Box<ConstantExpr>,
    new_var: &mut impl FnMut(Rvalue, Ty) -> Place,
) -> Operand {
    match val.kind {
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
            Operand::Const(val)
        }
        // Here we use a copy, rather than a move -- moving a global would leave it uninitialized,
        // which would e.g. make the following code fail:
        //     const GLOBAL: usize = 0;
        //     let x = GLOBAL;
        //     let y = GLOBAL; // if moving, at this point GLOBAL would be uninitialized
        ConstantExprKind::Global(global_ref) => {
            Operand::Copy(Place::new_global(global_ref, val.ty))
        }
        ConstantExprKind::PtrNoProvenance(ptr) => {
            let usize_ty = TyKind::Literal(LiteralTy::UInt(UIntTy::Usize)).into_ty();
            let ptr_usize = ConstantExprKind::Literal(Literal::Scalar(ScalarValue::Unsigned(
                UIntTy::Usize,
                ptr,
            )));
            let cast = UnOp::Cast(CastKind::RawPtr(usize_ty.clone(), val.ty.clone()));
            let uvar = new_var(
                Rvalue::UnaryOp(
                    cast,
                    Operand::Const(Box::new(ConstantExpr {
                        kind: ptr_usize,
                        ty: usize_ty,
                    })),
                ),
                val.ty,
            );
            Operand::Move(uvar)
        }
        ConstantExprKind::Ref(bval) => {
            match bval.kind {
                ConstantExprKind::Global(global_ref) => {
                    let unit_metadata = new_var(Rvalue::unit_value(), Ty::mk_unit());
                    Operand::Move(new_var(
                        // This is a reference to a global constant, which must be Sized, so no metadata
                        Rvalue::Ref {
                            place: Place::new_global(global_ref, bval.ty),
                            kind: BorrowKind::Shared,
                            ptr_metadata: Operand::Move(unit_metadata),
                        },
                        val.ty,
                    ))
                }
                _ => {
                    // Recurse on the borrowed value
                    let bval_ty = bval.ty.clone();
                    let bval = transform_constant_expr(span, bval, new_var);

                    // Evaluate the referenced value
                    let bvar = new_var(Rvalue::Use(bval), bval_ty);

                    let unit_metadata = new_var(Rvalue::unit_value(), Ty::mk_unit());

                    // Borrow the value
                    // As the value is originally an argument, it must be Sized
                    let ref_var = new_var(
                        Rvalue::Ref {
                            place: bvar,
                            kind: BorrowKind::Shared,
                            ptr_metadata: Operand::Move(unit_metadata),
                        },
                        val.ty,
                    );

                    Operand::Move(ref_var)
                }
            }
        }
        ConstantExprKind::Ptr(rk, bval) => {
            match bval.kind {
                ConstantExprKind::Global(global_ref) => {
                    let unit_metadata = new_var(Rvalue::unit_value(), Ty::mk_unit());
                    Operand::Move(new_var(
                        // This is a raw pointer to a global constant, which must be Sized, so no metadata
                        Rvalue::RawPtr {
                            place: Place::new_global(global_ref, bval.ty),
                            kind: rk,
                            ptr_metadata: Operand::Move(unit_metadata),
                        },
                        val.ty,
                    ))
                }
                _ => {
                    // Recurse on the borrowed value
                    let bval_ty = bval.ty.clone();
                    let bval = transform_constant_expr(span, bval, new_var);

                    // Evaluate the referenced value
                    let bvar = new_var(Rvalue::Use(bval), bval_ty);

                    let unit_metadata = new_var(Rvalue::unit_value(), Ty::mk_unit());

                    // Borrow the value
                    // As the value is originally an argument, it must be Sized, hence no metadata
                    let ref_var = new_var(
                        Rvalue::RawPtr {
                            place: bvar,
                            kind: rk,
                            ptr_metadata: Operand::Move(unit_metadata),
                        },
                        val.ty,
                    );

                    Operand::Move(ref_var)
                }
            }
        }
        ConstantExprKind::Adt(variant, fields) => {
            let fields = fields
                .into_iter()
                .map(|x| transform_constant_expr(span, Box::new(x), new_var))
                .collect();

            // Build an `Aggregate` rvalue.
            let rval = {
                let tref = val.ty.kind().as_adt().unwrap();
                let aggregate_kind = AggregateKind::Adt(tref.clone(), variant, None);
                Rvalue::Aggregate(aggregate_kind, fields)
            };
            let var = new_var(rval, val.ty);

            Operand::Move(var)
        }
        ConstantExprKind::Array(fields) => {
            let fields = fields
                .into_iter()
                .map(|x| transform_constant_expr(span, Box::new(x), new_var))
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
            let rval = Rvalue::Aggregate(AggregateKind::Array(ty, len), fields);
            let var = new_var(rval, val.ty);

            Operand::Move(var)
        }
    }
}

fn transform_operand(span: &Span, locals: &mut Locals, nst: &mut Vec<Statement>, op: &mut Operand) {
    // Transform the constant operands (otherwise do nothing)
    take_mut::take(op, |op| {
        if let Operand::Const(val) = op {
            let mut new_var = |rvalue, ty| {
                if let Rvalue::Use(Operand::Move(place)) = rvalue {
                    place
                } else {
                    let var = locals.new_var(None, ty);
                    nst.push(Statement::new(
                        *span,
                        StatementKind::Assign(var.clone(), rvalue),
                    ));
                    var
                }
            };
            transform_constant_expr(span, val, &mut new_var)
        } else {
            op
        }
    })
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut ExprBody) {
        for block in body.body.iter_mut() {
            // Deconstruct some constants into series of MIR assignments.
            block.transform_operands(|span, nst, op| {
                transform_operand(span, &mut body.locals, nst, op)
            });

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
