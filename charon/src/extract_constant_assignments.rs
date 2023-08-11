//! This module extracts globals from operands to put them in separate let bindings.
//! We do so to increase the sequentiality of LLBC and reduce the cases to handle
//! in the operands, making the formalisation less complex and easing the functional
//! translation in Aeneas.
//!
//! It also extracts statics fom operands for the same reason, because we want
//! to treat them as globals in (U)LLBC.
//! To do this, we add a new variable to reference the static: they are accessed
//! by reference in MIR, whereas globals are accessed by value.

use crate::expressions::*;
use crate::meta::Meta;
use crate::types::*;
use crate::ullbc_ast::{
    iter_function_bodies, iter_global_bodies, make_locals_generator, CtxNames, FunDecls,
    GlobalDecls, RawStatement, Statement,
};
use crate::ullbc_ast_utils::body_transform_operands;
use crate::values::VarId;

fn deref_static_type(ref_ty: &ETy) -> &ETy {
    match ref_ty {
        Ty::Ref(ErasedRegion::Erased, ty, RefKind::Shared) => ty,
        _ => unreachable!(
            "expected shared reference for static id type, got {:?}",
            ref_ty
        ),
    }
}

/// If the operand is a global identifier, push an `AssignGlobal` statement
/// that binds a new variable to the global and move it in the operand:
/// `... const X ...`
/// becomes
/// `let x0 = X;`
/// `... move x0 ...`
///
/// If the operand is a static global identifier, also add an indirection to take
/// a reference on it:
/// `... const X ...`
/// becomes
/// `let x0 = X;`
/// `let x1 = &X;`
/// `... move x1 ...`
fn extract_operand_global_var<F: FnMut(ETy) -> VarId::Id>(
    meta: &Meta,
    nst: &mut Vec<Statement>,
    op: &mut Operand,
    make_new_var: &mut F,
) {
    // Check for early return
    let (ty, c) = match op {
        Operand::Const(ty, c) => (ty, c),
        _ => return,
    };

    let var = match c {
        OperandConstantValue::Literal(_) | OperandConstantValue::Var(..) => return,
        OperandConstantValue::Adt(_, _) => {
            unreachable!("Constant ADTs should have been replaced by now")
        }
        OperandConstantValue::Global(global_id) => {
            let var = make_new_var(ty.clone());
            nst.push(Statement::new(
                *meta,
                RawStatement::Assign(Place::new(var), Rvalue::Global(*global_id)),
            ));
            var
        }
        OperandConstantValue::Ref(global) => {
            let global_id = *global.as_global();
            // TODO: we assume the constant value in the reference is a global.
            // We should generalize (probably by merging with regularize_constant_adts).
            let var = make_new_var(deref_static_type(ty).clone());
            let var_ref = make_new_var(ty.clone());
            let rvalue = Rvalue::Ref(Place::new(var), BorrowKind::Shared);
            nst.push(Statement::new(
                *meta,
                RawStatement::Assign(Place::new(var), Rvalue::Global(global_id)),
            ));
            nst.push(Statement::new(
                *meta,
                RawStatement::Assign(Place::new(var_ref), rvalue),
            ));
            var_ref
        }
    };
    *op = Operand::Move(Place::new(var));
}

pub fn transform(fmt_ctx: &CtxNames<'_>, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to extract global assignments: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );

        let mut f = make_locals_generator(&mut b.locals);
        body_transform_operands(&mut b.body, &mut |meta, nst, op| {
            extract_operand_global_var(meta, nst, op, &mut f)
        });
    }
}
