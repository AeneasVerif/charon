//! The MIR code often contains variables with type `Never`, and we want to get
//! rid of those. We proceed in two steps. First, we remove the instructions
//! `drop(v)` where `v` has type `Never` (it can happen - this module does the
//! filtering). Then, we filter the unused variables ([crate::remove_unused_locals]).

use take_mut::take;

use crate::llbc_ast::{transform_statements, CtxNames, FunDecls, GlobalDecls, Statement, Var};
use crate::ullbc_ast::{iter_function_bodies, iter_global_bodies};
use crate::values::*;

fn transform_st(locals: &VarId::Vector<Var>, st: Statement) -> Statement {
    // Shall we filter the statement?
    let filter = match &st {
        Statement::Drop(p) => {
            if p.projection.is_empty() {
                let var = locals.get(p.var_id).unwrap();
                var.ty.is_never()
            } else {
                false
            }
        }
        _ => false,
    };

    // If we filter the statement, we simply replace it with `nop`
    if filter {
        Statement::Nop
    } else {
        st
    }
}

/// `fmt_ctx` is used for pretty-printing purposes.
pub fn transform<'ctx>(fmt_ctx: &CtxNames<'ctx>, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to remove drops of variables with type ! in decl: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );

        let locals = &b.locals;

        // Compute the set of local variables
        take(&mut b.body, |b| {
            transform_statements(&mut |st| transform_st(locals, st), b)
        });
    }
}
