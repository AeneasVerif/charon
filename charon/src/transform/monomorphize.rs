//! # Micro-pass: monomorphize all functions and types; at the end of this pass, all functions and types are monomorphic.

use crate::transform::TransformCtx;
use crate::ullbc_ast::*;

use super::ctx::UllbcPass;

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // Check the option which instructs to ignore this pass
        if !ctx.options.monomorphize {
            return;
        }

        // From https://doc.rust-lang.org/nightly/nightly-rustc/rustc_monomorphize/collector/index.html#general-algorithm
        //
        // The purpose of the algorithm implemented in this module is to build the mono item
        // graph for the current crate. It runs in two phases:
        // 1. Discover the roots of the graph by traversing the HIR of the crate.
        // 2. Starting from the roots, find uses by inspecting the MIR representation of the
        //    item corresponding to a given node, until no more new nodes are found.
        //
        // The roots of the mono item graph correspond to the public non-generic syntactic
        // items in the source code. We find them by walking the HIR of the crate, and whenever
        // we hit upon a public function, method, or static item, we create a mono item
        // consisting of the items DefId and, since we only consider non-generic items, an
        // empty type-parameters set.
        //
        // Given a mono item node, we can discover uses by inspecting its MIR. We walk the MIR
        // to find other mono items used by each mono item. Since the mono item we are
        // currently at is always monomorphic, we also know the concrete type arguments of its
        // used mono items. The specific forms a use can take in MIR are quite diverse: it
        // includes calling functions/methods, taking a reference to a function/method, drop
        // glue, and unsizing casts.

        // In our version of the algorithm, we do the following:
        // 1. Find all the roots, adding them to the worklist.
        // 2. For each item in the worklist:
        //    a. Find all the items it uses, adding them to the worklist and the generic
        //      arguments to the item.
        //    b. Mark the item as visited

    }

    fn name(&self) -> &str {
        "monomorphize"
    }
}
