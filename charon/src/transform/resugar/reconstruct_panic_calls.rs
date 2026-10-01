//! Transform calls to builtin panicking functions into `TerminatorKind::Panic`.
use std::collections::HashMap;

use crate::ast::{Name, from_rustc, names};
use crate::transform::{CowBox, TransformCtx, ctx::UllbcPass};
use crate::ullbc_ast::*;

pub struct Transform {
    panic_fns: HashMap<FunDeclId, Name>,
}

impl Transform {
    pub fn new(ctx: &TransformCtx) -> CowBox<dyn UllbcPass> {
        let explicit_panic = Name::from_path(names::EXPLICIT_PANIC_NAME);
        let assert_failed = Name::from_path(&["core", "panicking", "assert_failed"]);
        let panic_fns = ctx
            .translated
            .fun_decls
            .iter_indexed()
            .filter_map(|(id, decl)| {
                // TODO: There are about 30 panic-related lang items. Decide which of the others
                // should also be reconstructed.
                let is_panic_lang_item = matches!(
                    decl.item_meta.lang_item,
                    Some(
                        from_rustc::LangItem::Panic
                            | from_rustc::LangItem::PanicFmt
                            | from_rustc::LangItem::BeginPanic
                    )
                );
                (is_panic_lang_item
                    || decl.item_meta.name == explicit_panic
                    || decl.item_meta.name == assert_failed)
                    .then(|| (id, decl.item_meta.name.clone()))
            })
            .collect();
        CowBox::Owned(Box::new(Self { panic_fns }))
    }
}

impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.reconstruct_panic_calls
    }

    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut ExprBody) {
        for block in &mut body.body {
            if let TerminatorKind::Call {
                call, on_unwind, ..
            } = &block.terminator.kind
                && let FnOperand::Regular(fn_ptr) = &call.func
                && let FnPtrKind::Fun(id) = fn_ptr.kind.as_ref()
                && let Some(name) = self.panic_fns.get(id)
            {
                block.terminator.kind = TerminatorKind::Panic {
                    name: name.clone(),
                    on_unwind: *on_unwind,
                };
            }
        }
    }
}
