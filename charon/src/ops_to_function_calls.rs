//! Desugar some unary/binary operations to function calls.
//! For instance, we desugar ArrayToSlice from an unop to a function call.
//! This allows a more uniform treatment later on.
//! TODO: actually transform all the unops and binops to function calls?

#![allow(dead_code)]

use crate::expressions::{Rvalue, UnOp};
use crate::formatter::Formatter;
use crate::llbc_ast::{iter_function_bodies, iter_global_bodies};
use crate::llbc_ast::{
    AssumedFunId, Call, FunDecls, FunIdOrTraitMethodRef, GlobalDecls, RawStatement, Statement,
};
use crate::translate_ctx::TransCtx;
use crate::types::ErasedRegion;
use crate::types::RefKind;

fn transform_st(s: &mut Statement) -> Vec<Statement> {
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
            let region_args = vec![ErasedRegion::Erased];
            let type_args = vec![ty.clone()];
            let const_generic_args = vec![cg.clone()];
            s.content = RawStatement::Call(Call {
                func,
                region_args,
                type_args,
                const_generic_args,
                trait_refs: Vec::new(),
                trait_and_method_generic_args: None,
                args: vec![op.clone()],
                dest: p.clone(),
            });

            vec![]
        }
        _ => vec![],
    }
}

pub fn transform(ctx: &TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to transform some operations to function calls: {name}:\n{}",
            ctx.format_object(&*b)
        );
        b.body.transform(&mut transform_st);
        trace!(
            "# After transforming some operations to function calls: {name}:\n{}",
            ctx.format_object(&*b)
        );
    }
}
