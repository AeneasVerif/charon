//! Remove the useless no-ops.

use crate::formatter::{Formatter, IntoFormatter};
use crate::llbc_ast::{RawStatement, Statement};
use crate::meta::combine_meta;
use crate::translate_ctx::TransformCtx;
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

pub fn transform(ctx: &mut TransformCtx) {
    ctx.iter_structured_bodies(|ctx, name, b| {
        let fmt_ctx = ctx.into_fmt();
        trace!(
            "# About to remove useless no-ops in decl: {}:\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );

        // Compute the set of local variables
        b.body.transform(&mut |st| {
            transform_st(st);
            None
        });
    })
}
