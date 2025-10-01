//! Remove the trait/impl methods that were not translated.
use crate::ast::*;

use crate::transform::{TransformCtx, ctx::TransformPass};

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let method_is_translated = |id: FunDeclId| ctx.translated.fun_decls.get(id).is_some();
        // Keep only the methods for which we translated the corresponding `FunDecl`. We ensured
        // that this would be translated if the method is used or transparently implemented.
        for tdecl in ctx.translated.trait_decls.iter_mut() {
            tdecl
                .methods
                .retain(|m| method_is_translated(m.skip_binder.item.id));
        }
        for timpl in ctx.translated.trait_impls.iter_mut() {
            timpl
                .methods
                .retain(|(_, m)| method_is_translated(m.skip_binder.id));
        }
    }
}
