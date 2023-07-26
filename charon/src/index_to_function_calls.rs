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
/// ```
/// // If array and mutable access:
/// ... p[i] ...
///    ~~>
/// tmp = ArrayMutIndex(&mut p, i)
/// ... *tmp ...
///
/// // If array and non-mutable access:
/// ... p[i] ...
///    ~~>
/// tmp = ArraySharedIndex(& p, i)
/// ... *tmp ...
///
/// // Omitting the slice cases, which are similar
/// ```
///
/// For instance, it leads to the following transformations:
/// ```
///   // x : [u32; N]
///   y : u32 = copy x[i]
///      ~~>
///   tmp : &u32 = ArraySharedIndex(&x, i)
///   y : u32 = copy (*tmp)
///
///   // x : &[T; N]
///   y : &T = & (*x)[i]
///      ~~>
///   tmp : &T = ArraySharedIndex(& (*x), i)
///   y : &T = & (*tmp)
///
///   // x : [u32; N]
///   y = &mut x[i]
///      ~~>
///   tmp = ArrayMutIndex(&mut x, i)
///   y = &mut (*tmp)
///
///   // y : [T; N]
///   y[i] = x
///      ~~>
///   tmp : &mut T = ArrayMutIndex(&mut y, i)
///   *y = x
///
///   // y : &mut [T; N]
///   (*y)[i] = x
///      ~~>
///   tmp : &mut T = ArrayMutIndex(&mut (*y), i)
///   *y = x
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
