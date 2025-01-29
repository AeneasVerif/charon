//! Remove the trait methods that were not translated.
use crate::ast::*;

use super::{ctx::TransformPass, TransformCtx};

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let method_is_translated = |(_, method): &(TraitItemName, Binder<FunDeclRef>)| {
            ctx.translated
                .fun_decls
                .get(method.skip_binder.id)
                .is_some()
        };
        // Keep only the methods for which we translated the corresponding `FunDecl`. We ensured
        // that this would be translated if the method is used or implemented.
        for tdecl in ctx.translated.trait_decls.iter_mut() {
            tdecl.provided_methods.retain(method_is_translated);
        }
    }
}
