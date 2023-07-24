//! Desugar some operations to function calls.
//! For instance, we desugar ArrayToSlice from an unop to a function call.
//! This allows a more uniform treatment later on.
//! TODO: actually transform all the unops and binops to function calls?

#![allow(dead_code)]

use crate::expressions::{MutExprVisitor, Rvalue, UnOp};
use crate::llbc_ast::{iter_function_bodies, iter_global_bodies};
use crate::llbc_ast::{
    AssumedFunId, Call, CtxNames, FunDecls, FunId, GlobalDecls, MutAstVisitor, RawStatement,
    Statement,
};

struct OpsToFunCall {}

impl MutExprVisitor for OpsToFunCall {}

impl MutAstVisitor for OpsToFunCall {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}

    fn visit_statement(&mut self, s: &mut Statement) {
        match &s.content {
            RawStatement::Assign(p, Rvalue::UnaryOp(UnOp::ArrayToSlice(ty, cg), op)) => {
                // We could avoid the clone operations below if we take the content of
                // the statement. In practice, this shouldn't have much impact.
                let func = FunId::Assumed(AssumedFunId::ArrayToSlice);
                let region_args = Vec::new();
                let type_args = vec![ty.clone()];
                let const_generic_args = vec![cg.clone()];
                s.content = RawStatement::Call(Call {
                    func,
                    region_args,
                    type_args,
                    const_generic_args,
                    args: vec![op.clone()],
                    dest: p.clone(),
                })
            }
            _ => self.default_visit_raw_statement(&mut s.content),
        }
    }
}

pub fn transform(fmt_ctx: &CtxNames<'_>, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to transform some operations to function calls: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
        let mut visitor = OpsToFunCall {};
        visitor.visit_statement(&mut b.body);
        trace!(
            "# After transforming some operations to function calls: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
    }
}
