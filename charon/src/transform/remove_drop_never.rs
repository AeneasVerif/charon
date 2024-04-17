//! The MIR code often contains variables with type `Never`, and we want to get
//! rid of those. We proceed in two steps. First, we remove the instructions
//! `drop(v)` where `v` has type `Never` (it can happen - this module does the
//! filtering). Then, we filter the unused variables ([crate::remove_unused_locals]).

use crate::formatter::{Formatter, IntoFormatter};
use crate::llbc_ast::{FunDecls, GlobalDecls, RawStatement, Statement, Var};
use crate::translate_ctx::TransCtx;
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

pub fn transform(ctx: &mut TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    ctx.iter_bodies(funs, globals, |ctx, name, b| {
        let fmt_ctx = ctx.into_fmt();
        trace!(
            "# About to remove drops of variables with type ! in decl: {}:\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );

        let locals = &b.locals;

        b.body.transform(&mut |st| {
            transform_st(locals, st);
            None
        });
    })
}
