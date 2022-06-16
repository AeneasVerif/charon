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

use lazy_static::__Deref;

use crate::common::update_mut;
use crate::expressions::*;
use crate::im_ast::{iter_function_bodies, iter_global_bodies};
use crate::llbc_ast::{FunDecls, GlobalDecls, Statement};
use crate::types::*;

/*fn is_constant_ADT(st: &Operand) -> bool {
    if let Operand::Const(_, c) = st {
        if let OperandConstantValue::Adt(_, _) = c {
            return true;
        }
    }
    false
}

fn make_projection(
    types: &TypeDecls,
    id: &TypeId,
    variant: &Option<VariantId::Id>,
    fields: &[ETy],
    index: usize,
) -> ProjectionElem {
    match id {
        TypeId::Tuple => {
            FieldProjKind::Tuple(fields.len());
            ProjectionElem::Field((), FieldId::Id::new(index))
        }
        TypeId::Adt(id) => {
            let ty = types.get_type_def(*id).unwrap();
            todo!()
        }
        TypeId::Assumed(_) => unreachable!(),
    }
}

fn expand_constant_ADT(ty: ETy, val: OperandConstantValue, dst: Place) -> Vec<Statement> {
    let (id, _, field_tys) = ty.as_adt();
    let (variant, fields_vals) = val.as_adt();

    let mut st = vec![];
    if let Some(v) = variant {
        st.push(Statement::SetDiscriminant(dst.clone(), *v));
    }
    for (i, (field_ty, field_val)) in zip(0..field_tys.len(), zip(field_tys, fields_vals)) {
        dst.projection
            .push_back(ProjectionElem::Field(FieldProjKind::AdtTuple(..), field_id));
        st.push(Statement::Assign(dst, ()));
    }
    st
}*/

fn print_op_constant_ADTs(op: &Operand) {
    if let Operand::Const(_, c) = op {
        if let OperandConstantValue::Adt(_, _) = c {
            println!("CONST ADT: {:?}", op);
        }
    }
}
fn print_st_constant_ADTs(st: &Statement) {
    match st {
        Statement::Assign(_, rval) => match rval {
            Rvalue::Use(op) => print_op_constant_ADTs(op),
            Rvalue::UnaryOp(_, op) => print_op_constant_ADTs(op),
            Rvalue::BinaryOp(_, o1, o2) => {
                print_op_constant_ADTs(&o1);
                print_op_constant_ADTs(&o2);
            }
            Rvalue::Aggregate(_, ops) => {
                for op in ops {
                    print_op_constant_ADTs(&op);
                }
            }
            _ => (),
        },
        Statement::Call(c) => {
            for arg in &c.args {
                print_op_constant_ADTs(arg);
            }
        }
        Statement::Switch(op, _) => print_op_constant_ADTs(op),
        Statement::Sequence(s1, s2) => {
            print_st_constant_ADTs(s1.deref());
            print_st_constant_ADTs(s2.deref());
        }
        Statement::Loop(s) => print_st_constant_ADTs(s.deref()),
        _ => (),
    }
}

/// Visit operands and generate a statement to extract the constant from it.
fn transform_st(st: Statement) -> Statement {
    match st {
        Statement::Assign(place, rval) => Statement::Assign(place, rval),
        Statement::Call(c) => Statement::Call(c),
        Statement::Switch(op, tgt) => Statement::Switch(op, tgt),

        Statement::Sequence(s1, s2) => {
            Statement::Sequence(Box::new(transform_st(*s1)), Box::new(transform_st(*s2)))
        }
        Statement::Loop(s) => Statement::Loop(Box::new(transform_st(*s))),
        st => st,
    }
}

pub fn transform(_types: &TypeDecls, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        println!("# CHECK IN {name}");
        print_st_constant_ADTs(&b.body);
        update_mut(&mut b.body, transform_st);
    }
    // TODO: Visit bodies to check that there are no ADT left.
}
