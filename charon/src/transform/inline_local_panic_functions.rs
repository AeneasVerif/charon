//! `panic!()` expands to:
//! ```ignore
//! fn panic_cold_explicit() -> ! {
//!     core::panicking::panic_explicit()
//! }
//! panic_cold_explicit()
//! ```
//! Which defines a new function each time. This pass recognizes these functions and replaces calls
//! to them by a `Panic` terminator.
use std::collections::HashSet;

use super::{ctx::UllbcPass, TransformCtx};
use crate::{builtins, names::Name, ullbc_ast::*};

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // Collect the functions that were generated by the `panic!` macro.
        let mut panic_fns = HashSet::new();
        ctx.for_each_fun_decl(|_ctx, decl| {
            if let Ok(body) = &mut decl.body {
                let body = body.as_unstructured().unwrap();
                // If the whole body is only a call to this specific panic function.
                if body.body.elem_count() == 1
                    && let Some(block) = body.body.iter().next()
                    && block.statements.is_empty()
                    && let RawTerminator::Abort(AbortKind::Panic(Some(name))) =
                        &block.terminator.content
                {
                    if name.equals_ref_name(builtins::EXPLICIT_PANIC_NAME) {
                        // FIXME: also check that the name of the function is
                        // `panic_cold_explicit`?
                        panic_fns.insert(decl.def_id);
                    }
                }
            }
        });

        let panic_name = Name::from_path(builtins::EXPLICIT_PANIC_NAME);
        let panic_terminator = RawTerminator::Abort(AbortKind::Panic(Some(panic_name)));

        // Replace each call to one such function with a `Panic`.
        ctx.for_each_fun_decl(|_ctx, decl| {
            if let Ok(body) = &mut decl.body {
                let body = body.as_unstructured_mut().unwrap();
                for block_id in body.body.all_indices() {
                    let Some(block) = body.body.get_mut(block_id) else {
                        continue;
                    };
                    for i in 0..block.statements.len() {
                        let st = &block.statements[i];
                        if let RawStatement::Call(Call {
                            func:
                                FnOperand::Regular(FnPtr {
                                    func: FunIdOrTraitMethodRef::Fun(FunId::Regular(fun_id)),
                                    ..
                                }),
                            ..
                        }) = &st.content
                            && panic_fns.contains(fun_id)
                        {
                            block.statements.drain(i..);
                            block.terminator.content = panic_terminator.clone();
                            break;
                        }
                    }
                }
            }
        });

        // Remove these functions from the context.
        for id in &panic_fns {
            ctx.translated.fun_decls.remove(*id);
        }
    }
}
