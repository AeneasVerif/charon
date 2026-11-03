//! Resugar direct calls to `Drop::drop` for `Box`.
//!
//! Dropping an initialized Box uses drop terminators like any other value. However Box is special:
//! it allows being moved out of. When a partially-moved-out-of Box reaches end of scope, drop
//! elaboration destructs the rest of the value, then calls `Drop::drop` directly, which is atypical.
//!
//! This pass recovers this into a builtin operation.
use crate::transform::{TransformCtx, ctx::UllbcPass};
use crate::ullbc_ast::*;

pub struct Transform;

fn trait_ref_is_box_drop(krate: &TranslatedCrate, trait_ref: &TraitDeclRef) -> bool {
    krate
        .trait_decls
        .get(trait_ref.id)
        .is_some_and(|decl| decl.item_meta.lang_item == Some(from_rustc::LangItem::Drop))
        && trait_ref.self_ty(krate).is_some_and(|ty| ty.is_box())
}

impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.treat_box_as_builtin && !options.desugar_drops
    }

    fn transform_body(&self, ctx: &mut TransformCtx, body: &mut ExprBody) {
        let krate: &TranslatedCrate = &ctx.translated;
        for block in &mut body.body {
            if let TerminatorKind::Call {
                call,
                target,
                on_unwind,
                ..
            } = &block.terminator.kind
                && let FnOperand::Regular(fn_ptr) = &call.func
                && fn_ptr
                    .as_method_call(krate)
                    .is_some_and(|(tref, _)| trait_ref_is_box_drop(krate, tref))
                && let [Operand::Move(argument)] = call.args.as_slice()
                && let Some(statement) = block.statements.last()
                && let StatementKind::Assign(
                    temporary,
                    Rvalue::Ref {
                        place,
                        kind: BorrowKind::Mut,
                        ..
                    },
                ) = &statement.kind
                && temporary.is_local()
                && temporary == argument
                && place.ty().is_box()
            {
                let place = place.clone();
                let target = *target;
                let on_unwind = *on_unwind;
                block.statements.pop();
                block.terminator.kind = TerminatorKind::DropEmptyBox {
                    place,
                    target,
                    on_unwind,
                };
            }
        }
    }
}
