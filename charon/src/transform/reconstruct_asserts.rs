//! In the MIR AST, it seems `assert` are introduced to check preconditions
//! (for the binops for example). The `assert!` introduced by the user
//! introduce `if ... then { panic!(...) } else { ...}`.
//! This pass introduces `assert` instead in order to make the code shorter.

use take_mut::take;

use crate::formatter::{Formatter, IntoFormatter};
use crate::llbc_ast::*;
use crate::pretty::FmtWithCtx;
use crate::transform::TransformCtx;

fn transform_st(st: &mut Statement) -> Option<Vec<Statement>> {
    if let RawStatement::Switch(Switch::If(_, st1, _)) = &mut st.content {
        // Check if the first statement is a panic: if yes, replace
        // the if .. then ... else ... by an assertion.
        if st1.content.is_panic() {
            // Replace: we need to take the value
            take(&mut st.content, |st| {
                let (op, st1, st2) = st.to_switch().to_if();
                let st1 = Statement::new(
                    st1.span,
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

pub fn transform(ctx: &mut TransformCtx) {
    ctx.iter_structured_bodies(|ctx, name, b| {
        let fmt_ctx = ctx.into_fmt();
        trace!(
            "# About to reconstruct asserts in decl: {}\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );
        b.body.transform(&mut transform_st);
    })
}
