//! Extracts globals from operands to put them in a separate let binding.
//! This is done to increase sequentiality of LLBC :
//! It will ease the functional translation.

use crate::common::update_mut;
use crate::expressions::*;
use crate::im_ast::{iter_function_bodies, iter_global_bodies, make_locals_generator};
use crate::llbc_ast::{Assert, Call, FunDecls, GlobalDecls, Statement};
use crate::llbc_ast_utils::chain_statements;
use crate::types::*;
use crate::values::VarId;

/// If the operand is a constant global identifier, returns an `AssignGlobal` statement
/// that binds a new variable to the global and move it in the operand.
fn extract_operand_global_var<F: FnMut(ETy) -> VarId::Id>(
    op: &mut Operand,
    make_new_var: &mut F,
) -> Option<Statement> {
    if let Operand::Const(ty, c) = op {
        if let OperandConstantValue::Identifier(global_id) = *c {
            // Make the new variable for the operand & assignment.
            let var_id = make_new_var(ty.clone());
            *op = Operand::Move(Place {
                var_id,
                projection: im::Vector::new(),
            });
            return Some(Statement::AssignGlobal(var_id, global_id));
        }
    }
    None
}

// Small utilities to have an uniform interface.
fn extract_op_global<F: FnMut(&mut Operand) -> Option<Statement>>(
    op: &mut Operand,
    f: &mut F,
) -> Vec<Statement> {
    f(op).into_iter().collect()
}
fn extract_assert_op_global<F: FnMut(&mut Operand) -> Option<Statement>>(
    a: &mut Assert,
    f: &mut F,
) -> Vec<Statement> {
    extract_op_global(&mut a.cond, f)
}
fn extract_call_op_globals<F: FnMut(&mut Operand) -> Option<Statement>>(
    c: &mut Call,
    f: &mut F,
) -> Vec<Statement> {
    c.args.iter_mut().map(f).flatten().collect()
}
fn extract_rvalue_op_globals<F: FnMut(&mut Operand) -> Option<Statement>>(
    rval: &mut Rvalue,
    f: &mut F,
) -> Vec<Statement> {
    match rval {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) => extract_op_global(op, f),
        Rvalue::BinaryOp(_, o1, o2) => vec![f(o1), f(o2)].into_iter().flatten().collect(),
        Rvalue::Aggregate(_, ops) => ops.iter_mut().map(f).flatten().collect(),
        Rvalue::Discriminant(_) | Rvalue::Ref(_, _) => vec![],
    }
}

fn transform_st<F: FnMut(&mut Operand) -> Option<Statement>>(
    st: Statement,
    f: &mut F,
) -> Statement {
    // Does two matchs, depending if we want to move or to borrow the statement.
    let mut st = match st {
        // Recursive calls
        Statement::Loop(s) => Statement::Loop(Box::new(transform_st(*s, f))),
        Statement::Sequence(s1, s2) => Statement::Sequence(
            Box::new(transform_st(*s1, f)),
            Box::new(transform_st(*s2, f)),
        ),
        _ => st,
    };
    match &mut st {
        // Actual transformations
        Statement::Switch(op, _) => chain_statements(extract_op_global(op, f), st),
        Statement::Assign(_, r) => chain_statements(extract_rvalue_op_globals(r, f), st),
        Statement::Call(c) => chain_statements(extract_call_op_globals(c, f), st),
        Statement::Assert(a) => chain_statements(extract_assert_op_global(a, f), st),

        Statement::AssignGlobal(_, _) => {
            unreachable!("global assignments should only be created after this pass")
        }

        // Identity (complete match for compile-time errors when new statements are created)
        Statement::FakeRead(_)
        | Statement::SetDiscriminant(_, _)
        | Statement::Drop(_)
        | Statement::Panic
        | Statement::Return
        | Statement::Break(_)
        | Statement::Continue(_)
        | Statement::Nop
        | Statement::Sequence(_, _)
        | Statement::Loop(_) => st,
    }
}

pub fn transform(funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!("# About to extract global assignments: {name}");

        let mut f = make_locals_generator(&mut b.locals);
        update_mut(&mut b.body, |st| {
            transform_st(st, &mut |op| extract_operand_global_var(op, &mut f))
        });
    }
}
