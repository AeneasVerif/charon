//! The MIR constant expressions lead to a lot of duplication: there are
//! for instance constant ADTs which duplicate the "regular" aggregated
//! ADTs in the operands, constant references, etc. This reduces the number
//! of cases to handle and eases the function translation in Aeneas.
//!
//! This pass removes all those occurrences so that only the
//! [ConstantExpression::Literal]. It does so by introducing intermediate statements.
//!
//! A small remark about the intermediate statements we introduce for the globals:
//! we do so because, when evaluating the code in "concrete" mode, it allows to
//! handle the globals like function calls.

use crate::expressions::*;
use crate::meta::Span;
use crate::transform::TransformCtx;
use crate::types::*;
use crate::ullbc_ast::{
    body_transform_operands, make_locals_generator, ExprBody, RawStatement, Statement,
};
use crate::values::VarId;

use super::ctx::UllbcPass;

fn make_aggregate_kind(ty: &Ty, var_index: Option<VariantId>) -> AggregateKind {
    let (id, generics) = ty.as_adt();
    AggregateKind::Adt(*id, var_index, generics.clone())
}

/// If the constant value is a constant ADT, push `Assign::Aggregate` statements
/// to the vector of statements, that bind new variables to the ADT parts and
/// the variable assigned to the complete ADT.
///
/// Goes fom e.g. `f(T::A(x, y))` to `let a = T::A(x, y); f(a)`.
/// The function is recursively called on the aggregate fields (e.g. here x and y).
fn transform_constant_expr<F: FnMut(Ty) -> VarId>(
    span: &Span,
    nst: &mut Vec<Statement>,
    val: ConstantExpr,
    make_new_var: &mut F,
) -> Operand {
    match val.value {
        RawConstantExpr::Literal(_)
        | RawConstantExpr::Var(_)
        | RawConstantExpr::TraitConst(..)
        | RawConstantExpr::FnPtr(..) => {
            // Nothing to do
            // TODO: for trait const: might come from a top-level impl, so we might
            // want to introduce an intermediate statement to be able to evaluate
            // it as a function call, like for globals.
            Operand::Const(val)
        }
        RawConstantExpr::Global(global_id, substs) => {
            // Introduce an intermediate statement
            let var_id = make_new_var(val.ty.clone());
            nst.push(Statement::new(
                *span,
                RawStatement::Assign(Place::new(var_id), Rvalue::Global(global_id, substs)),
            ));
            Operand::Move(Place::new(var_id))
        }
        RawConstantExpr::Ref(box bval) => {
            // Recurse on the borrowed value
            let bval_ty = bval.ty.clone();
            let bval = transform_constant_expr(span, nst, bval, make_new_var);

            // Introduce an intermediate statement to evaluate the referenced value
            let bvar_id = make_new_var(bval_ty);
            nst.push(Statement::new(
                *span,
                RawStatement::Assign(Place::new(bvar_id), Rvalue::Use(bval)),
            ));

            // Introduce an intermediate statement to borrow the value
            let ref_var_id = make_new_var(val.ty);
            let rvalue = Rvalue::Ref(Place::new(bvar_id), BorrowKind::Shared);
            nst.push(Statement::new(
                *span,
                RawStatement::Assign(Place::new(ref_var_id), rvalue),
            ));

            // Return the new operand
            Operand::Move(Place::new(ref_var_id))
        }
        RawConstantExpr::Adt(variant, fields) => {
            // Recurse on the fields
            let fields = fields
                .into_iter()
                .map(|f| transform_constant_expr(span, nst, f, make_new_var))
                .collect();

            // Introduce an intermediate assignment for the aggregated ADT
            let rval = Rvalue::Aggregate(make_aggregate_kind(&val.ty, variant), fields);
            let var_id = make_new_var(val.ty);
            nst.push(Statement::new(
                *span,
                RawStatement::Assign(Place::new(var_id), rval),
            ));

            // Return the new operand
            Operand::Move(Place::new(var_id))
        }
    }
}

fn transform_operand<F: FnMut(Ty) -> VarId>(
    span: &Span,
    nst: &mut Vec<Statement>,
    op: &mut Operand,
    f: &mut F,
) {
    // Transform the constant operands (otherwise do nothing)
    take_mut::take(op, |op| {
        if let Operand::Const(val) = op {
            transform_constant_expr(span, nst, val, f)
        } else {
            op
        }
    })
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        let mut f = make_locals_generator(&mut b.locals);
        body_transform_operands(&mut b.body, &mut |span, nst, op| {
            transform_operand(span, nst, op, &mut f)
        });
    }
}
