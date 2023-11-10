//! In the MIR AST, it seems `assert` are introduced to check preconditions
//! (for the binops for example). The `assert!` introduced by the user
//! introduce `if ... then { panic!(...) } else { ...}`.
//! This pass introduces `assert` instead in order to make the code shorter.

use take_mut::take;

use crate::formatter::Formatter;
use crate::gast::{iter_function_bodies, iter_global_bodies};
use crate::llbc_ast::*;
use crate::translate_ctx::TransCtx;

fn transform_st(st: &mut Statement) -> Option<Vec<Statement>> {
    if let RawStatement::Switch(Switch::If(_, st1, _)) = &mut st.content {
        // Check if the first statement is a panic: if yes, replace
        // the if .. then ... else ... by an assertion.
        if st1.content.is_panic() {
            // Replace: we need to take the value
            take(&mut st.content, |st| {
                let (op, st1, st2) = st.to_switch().to_if();
                let st1 = Statement::new(
                    st1.meta,
                    RawStatement::Assert(Assert {
                        cond: op,
                        expected: false,
                    }),
                );
                let st1 = Box::new(st1);
                RawStatement::Sequence(st1, st2)
            });
        }
    }
    None
}

pub fn transform(ctx: &TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to reconstruct asserts in decl: {name}\n{}",
            ctx.format_object(&*b)
        );
        b.body.transform(&mut transform_st);
    }
}
