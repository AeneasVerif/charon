//! Remove the useless no-ops.

use crate::formatter::Formatter;
use crate::llbc_ast::{FunDecls, GlobalDecls, RawStatement, Statement};
use crate::meta::combine_meta;
use crate::translate_ctx::TransCtx;
use crate::ullbc_ast::{iter_function_bodies, iter_global_bodies};
use take_mut::take;

fn transform_st(s: &mut Statement) {
    if let RawStatement::Sequence(s1, _) = &s.content {
        if s1.content.is_nop() {
            take(s, |s| {
                let (s1, s2) = s.content.to_sequence();
                Statement {
                    content: s2.content,
                    meta: combine_meta(&s1.meta, &s2.meta),
                }
            })
        }
    }
}

pub fn transform(ctx: &TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to remove useless no-ops in decl: {}:\n{}",
            name.fmt_with_ctx(ctx),
            ctx.format_object(&*b)
        );

        // Compute the set of local variables
        b.body.transform(&mut |st| {
            transform_st(st);
            None
        });
    }
}
