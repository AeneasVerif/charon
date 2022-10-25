//! In MIR, compile-time constant ADTs are treated separately.
//! We don't want to have this distinction / redundancy in LLBC.
//!
//! This pass removes all occurrences of [OperandConstantValue::Adt],
//! and builds regular ADTs ([Rvalue::Aggregate]) instead (as for static values).
//!
//! To do so, it recursively translates an operand of the form `const <ADT>`
//! to `AggregatedAdt`. The recursion happens on the assignment operands.

use std::iter::zip;

use crate::expressions::*;
use crate::llbc_ast::{CtxNames, FunDecls, GlobalDecls, RawStatement, Statement};
use crate::llbc_ast_utils::transform_operands;
use crate::meta::Meta;
use crate::types::*;
use crate::ullbc_ast::{iter_function_bodies, iter_global_bodies, make_locals_generator};
use crate::values::VarId;
use take_mut::take;

fn make_aggregate_kind(ty: &ETy, var_index: Option<VariantId::Id>) -> AggregateKind {
    let (id, _, fields) = ty.as_adt();
    match id {
        TypeId::Tuple => {
            assert!(var_index.is_none());
            AggregateKind::Tuple
        }
        TypeId::Adt(decl_id) => {
            let fields = fields.iter().cloned().collect();
            AggregateKind::Adt(*decl_id, var_index, vec![], fields)
        }
        TypeId::Assumed(_) => unreachable!(),
    }
}

/// If the constant value is a constant ADT, returns `Assign::Aggregate` statements that
/// binds new variables to the ADT parts and the variable assigned to the complete ADT.
///
/// Goes fom e.g. `f(T::A(x, y))` to `let a = T::A(x, y); f(a)`.
/// The function is recursively called on the aggregate fields (e.g. here x and y).
fn transform_constant_adt<F: FnMut(ETy) -> VarId::Id>(
    meta: &Meta,
    ty: &ETy,
    val: &OperandConstantValue,
    make_new_var: &mut F,
) -> Option<(Vec<Statement>, VarId::Id)> {
    let (variant, fields) = match val {
        OperandConstantValue::Adt(v, f) => (v, f),
        _ => return None,
    };

    // Translate fields recursively into statements and operands.
    let mut statements = vec![];
    let ops = zip(ty.as_adt().2, fields)
        .map(|(f_ty, f_val)| {
            if let Some((mut st, var_id)) = transform_constant_adt(meta, f_ty, f_val, make_new_var)
            {
                statements.append(&mut st);
                Operand::Move(Place::new(var_id))
            } else {
                Operand::Const(f_ty.clone(), f_val.clone())
            }
        })
        .collect();

    // Make the new variable holding the aggregate.
    let rval = Rvalue::Aggregate(make_aggregate_kind(ty, *variant), ops);
    let var_id = make_new_var(ty.clone());
    statements.push(Statement::new(
        meta.clone(),
        RawStatement::Assign(Place::new(var_id), rval),
    ));
    Some((statements, var_id))
}

fn transform_operand_adt<F: FnMut(ETy) -> VarId::Id>(
    meta: &Meta,
    op: &mut Operand,
    f: &mut F,
) -> Vec<Statement> {
    if let Operand::Const(ty, val) = op {
        if let Some((st, var_id)) = transform_constant_adt(meta, ty, val, f) {
            // Change the ADT constant operand to a move (of the extracted AST).
            *op = Operand::Move(Place::new(var_id));
            return st;
        }
    }
    vec![]
}

pub fn transform<'ctx>(fmt_ctx: &CtxNames<'ctx>, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to regularize constant ADTs in function: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );

        let mut f = make_locals_generator(&mut b.locals);
        take(&mut b.body, |st| {
            transform_operands(st, &mut |meta, op| transform_operand_adt(meta, op, &mut f))
        });
    }
}
