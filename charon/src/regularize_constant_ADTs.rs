//! In MIR, compile-time constant ADTs are treated separately.
//! We don't want to have this distinction / redundancy in LLBC :
//!
//! This pass removes all occurrences of OperandConstantValue::ConstantAdt,
//! and builds regular ADTs instead (as for static values).
//!
//! To do so, it recursively translate an operand of the form
//! `... const ADT ...;`
//! to something like
//! `SetDiscriminant(_new_var, N);` (in the case of enums)
//! `Assign(_new_var.N, operand);`
//! `... const ADT ...;`
//! The recursion happens on the assignment operands.

use std::iter::zip;

use itertools::chain;

use crate::common::update_mut;
use crate::expressions::*;
use crate::im_ast::{iter_function_bodies, iter_global_bodies, make_locals_generator};
use crate::llbc_ast::{FunDecls, GlobalDecls, Statement};
use crate::llbc_ast_utils::chain_statements;
use crate::types::*;
use crate::values::VarId;

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
fn translate_constant_adt<F: FnMut(ETy) -> VarId::Id>(
    ty: &ETy,
    val: &OperandConstantValue,
    make_new_var: &mut F,
) -> Option<(Vec<Statement>, VarId::Id)> {
    let (variant, fields) = match val {
        OperandConstantValue::Adt(v, f) => (v, f),
        _ => return None,
    };

    println!("GOT CONST ADT: {:?}", fields);

    // Translate fields recursively into statements and operands.
    let mut statements = vec![];
    let ops = zip(ty.as_adt().2, fields)
        .map(|(f_ty, f_val)| {
            if let Some((mut st, var_id)) = translate_constant_adt(f_ty, f_val, make_new_var) {
                statements.append(&mut st);
                Operand::Move(Place {
                    var_id,
                    projection: im::Vector::new(),
                })
            } else {
                Operand::Const(f_ty.clone(), f_val.clone())
            }
        })
        .collect();

    // Make the new variable holding the aggregate.
    let rval = Rvalue::Aggregate(make_aggregate_kind(ty, *variant), ops);
    let var_id = make_new_var(ty.clone());
    let place = Place {
        var_id,
        projection: im::Vector::new(),
    };
    statements.push(Statement::Assign(place, rval));
    Some((statements, var_id))
}

fn translate_operand_adt<F: FnMut(ETy) -> VarId::Id>(
    op: &mut Operand,
    f: &mut F,
) -> Vec<Statement> {
    if let Operand::Const(ty, val) = op {
        if let Some((st, var_id)) = translate_constant_adt(ty, val, f) {
            // Change the ADT constant operand to a move (of the extracted AST).
            *op = Operand::Move(Place {
                var_id,
                projection: im::Vector::new(),
            });
            return st;
        }
    }
    vec![]
}

fn extract_rvalue_op_adts<F: FnMut(&mut Operand) -> Vec<Statement>>(
    rval: &mut Rvalue,
    f: &mut F,
) -> Vec<Statement> {
    match rval {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) => f(op),
        Rvalue::BinaryOp(_, o1, o2) => chain(f(o1), f(o2)).collect(),
        Rvalue::Aggregate(_, ops) => ops.iter_mut().flat_map(f).collect(),
        Rvalue::Discriminant(_) | Rvalue::Ref(_, _) => vec![],
    }
}

/// Visit operands and generate statements to extract the ADTs from it.
fn transform_st<F: FnMut(&mut Operand) -> Vec<Statement>>(st: Statement, f: &mut F) -> Statement {
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
        Statement::Switch(op, _) => chain_statements(f(op), st),
        Statement::Assign(_, r) => chain_statements(extract_rvalue_op_adts(r, f), st),
        Statement::Call(c) => chain_statements(c.args.iter_mut().flat_map(f).collect(), st),
        Statement::Assert(a) => chain_statements(f(&mut a.cond), st),

        Statement::AssignGlobal(_, _) => {
            unreachable!("global assignments should append after this pass")
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
        trace!("# About to regularize constant ADTs: {name}");

        let mut f = make_locals_generator(&mut b.locals);
        update_mut(&mut b.body, |st| {
            transform_st(st, &mut |op| translate_operand_adt(op, &mut f))
        });
    }
}
