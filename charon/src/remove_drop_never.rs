//! The MIR code often contains variables with type `Never`, and we want to get
//! rid of those. We proceed in two steps. First, we remove the instructions
//! `drop(v)` where `v` has type `Never` (it can happen - this module does the
//! filtering). Then, we filter the unused variables ([crate::remove_unused_locals]).

use crate::formatter::Formatter;
use crate::llbc_ast::{FunDecls, GlobalDecls, RawStatement, Statement, Var};
use crate::translate_ctx::TransCtx;
use crate::ullbc_ast::{iter_function_bodies, iter_global_bodies};
use crate::values::*;

/// Filter the statement by replacing it with `Nop` if it is a `Drop(x)` where
/// `x` has type `Never`. Otherwise leave it unchanged.
fn transform_st(locals: &VarId::Vector<Var>, st: &mut Statement) {
    // Shall we filter the statement?
    let filter = match &mut st.content {
        RawStatement::Drop(p) => {
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
        *st = Statement::new(st.meta, RawStatement::Nop);
    }
}

/// `fmt_ctx` is used for pretty-printing purposes.
pub fn transform(ctx: &TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to remove drops of variables with type ! in decl: {name}:\n{}",
            ctx.format_object(&*b)
        );

        let locals = &b.locals;

        // Compute the set of local variables
        b.body.transform(&mut |st| {
            transform_st(locals, st);
            None
        });
    }
}
