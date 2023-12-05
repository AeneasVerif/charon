//! Desugar some unary/binary operations and the array repeats to function calls.
//! For instance, we desugar ArrayToSlice from an unop to a function call.
//! This allows a more uniform treatment later on.
//! TODO: actually transform all the unops and binops to function calls?
use crate::expressions::{Rvalue, UnOp};
use crate::formatter::{Formatter, IntoFormatter};
use crate::llbc_ast::*;
use crate::translate_ctx::TransCtx;
use crate::types::*;

fn transform_st(s: &mut Statement) -> Option<Vec<Statement>> {
    match &s.content {
        // Transform the ArrayToSlice unop
        RawStatement::Assign(p, Rvalue::UnaryOp(UnOp::ArrayToSlice(ref_kind, ty, cg), op)) => {
            // We could avoid the clone operations below if we take the content of
            // the statement. In practice, this shouldn't have much impact.
            let id = match ref_kind {
                RefKind::Mut => AssumedFunId::ArrayToSliceMut,
                RefKind::Shared => AssumedFunId::ArrayToSliceShared,
            };
            let func = FunIdOrTraitMethodRef::mk_assumed(id);
            let generics = GenericArgs::new(
                vec![Region::Erased],
                vec![ty.clone()],
                vec![cg.clone()],
                vec![],
            );
            let func = FnOperand::Regular(FnPtr {
                func,
                generics,
                trait_and_method_generic_args: None,
            });
            s.content = RawStatement::Call(Call {
                func,
                args: vec![op.clone()],
                dest: p.clone(),
            });

            None
        }
        // Transform the array aggregates to function calls
        RawStatement::Assign(p, Rvalue::Repeat(op, ty, cg)) => {
            // We could avoid the clone operations below if we take the content of
            // the statement. In practice, this shouldn't have much impact.
            let id = AssumedFunId::ArrayRepeat;
            let func = FunIdOrTraitMethodRef::mk_assumed(id);
            let generics = GenericArgs::new(
                vec![Region::Erased],
                vec![ty.clone()],
                vec![cg.clone()],
                vec![],
            );
            let func = FnOperand::Regular(FnPtr {
                func,
                generics,
                trait_and_method_generic_args: None,
            });
            s.content = RawStatement::Call(Call {
                func,
                args: vec![op.clone()],
                dest: p.clone(),
            });

            None
        }
        _ => None,
    }
}

pub fn transform(ctx: &TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    let fmt_ctx = ctx.into_fmt();
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to transform some operations to function calls: {}:\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );
        b.body.transform(&mut transform_st);
        trace!(
            "# After transforming some operations to function calls: {}:\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );
    }
}
