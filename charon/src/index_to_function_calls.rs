//! Desugar array/slice index operations to function calls.

#![allow(dead_code)]

use crate::expressions::{MutExprVisitor, Rvalue, UnOp};
use crate::llbc_ast::{iter_function_bodies, iter_global_bodies};
use crate::llbc_ast::{
    AssumedFunId, Call, CtxNames, FunDecls, FunId, GlobalDecls, MutAstVisitor, RawStatement,
    Statement,
};

struct IndexToFunCall {}

impl MutExprVisitor for IndexToFunCall {}

impl MutAstVisitor for IndexToFunCall {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}

    fn visit_statement(&mut self, s: &mut Statement) {
        todo!()
    }
}

/// We do the following.
///
/// If `p` is a projection (for instance: `var`, `*var`, `var.f`, etc.), we
/// detect:
/// - whether it operates on a slice or an array (we keep track of the types)
/// - whether the access might mutate the value or not (it is
///   the case if it is in a `move`, `&mut` or at the lhs of an assignment),
///   and do the following transformations
///
/// ```text
///   // If array and mutable access:
///   ... p[i] ...
///      ~~>
///   tmp0 = &mut p
///   tmp1 = ArrayMutIndex(move p, i)
///   ... *tmp1 ...
///
///   // If array and non-mutable access:
///   ... p[i] ...
///      ~~>
///   tmp0 := & p
///   tmp1 := ArraySharedIndex(move tmp0, i)
///   ... *tmp1 ...
///
///   // Omitting the slice cases, which are similar
/// ```
///
/// For instance, it leads to the following transformations:
/// ```text
///   // x : [u32; N]
///   y : u32 = copy x[i]
///      ~~>
///   tmp0 : & [u32; N] := &x
///   tmp1 : &u32 = ArraySharedIndex(move tmp0, i)
///   y : u32 = copy (*tmp1)
///
///   // x : &[T; N]
///   y : &T = & (*x)[i]
///      ~~>
///   tmp0 : & [T; N] := & (*x)
///   tmp1 : &T = ArraySharedIndex(move tmp0, i)
///   y : &T = & (*tmp1)
///
///   // x : [u32; N]
///   y = &mut x[i]
///      ~~>
///   tmp0 : &mut [u32; N] := &mut x
///   tmp1 : &mut u32 := ArrayMutIndex(move tmp0, i)
///   y = &mut (*tmp)
///
///   // When using an index on the lhs:
///   // y : [T; N]
///   y[i] = x
///      ~~>
///   tmp0 : &mut [T; N] := &mut y;
///   tmp1 : &mut T = ArrayMutIndex(move y, i)
///   *tmp1 = x
/// ```
pub fn transform(fmt_ctx: &CtxNames<'_>, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to transform array/slice index operations to function calls: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
        let mut visitor = IndexToFunCall {};
        visitor.visit_statement(&mut b.body);
        trace!(
            "# After transforming array/slice index operations to function calls: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
    }
}
