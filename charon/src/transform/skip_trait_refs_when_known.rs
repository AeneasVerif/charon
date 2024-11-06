use crate::{transform::TransformCtx, ullbc_ast::*};

use super::ctx::UllbcPass;

fn transform_call(ctx: &TransformCtx, call: &mut Call) {
    // We find calls to a trait method where the impl is known; otherwise we return.
    let FnOperand::Regular(fn_ptr) = &mut call.func else {
        return;
    };
    let FunIdOrTraitMethodRef::Trait(trait_ref, name, _) = &fn_ptr.func else {
        return;
    };
    let TraitRefKind::TraitImpl(impl_id, impl_generics) = &trait_ref.kind else {
        return;
    };
    let Some(trait_impl) = &ctx.translated.trait_impls.get(*impl_id) else {
        return;
    };
    // Find the function declaration corresponding to this impl.
    let Some((_, fun_decl_id)) = trait_impl
        .required_methods
        .iter()
        .chain(trait_impl.provided_methods.iter())
        .find(|(n, _)| n == name)
    else {
        return;
    };
    let fn_generics = &fn_ptr.generics;
    // Move the trait generics to the function call.
    // FIXME: make a better API than `concat`.
    fn_ptr.generics = impl_generics.clone().concat(fn_generics);
    // Set the call operation to use the function directly.
    fn_ptr.func = FunIdOrTraitMethodRef::Fun(FunId::Regular(*fun_decl_id));
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, ctx: &mut TransformCtx, b: &mut ExprBody) {
        for block in b.body.iter_mut() {
            for st in block.statements.iter_mut() {
                if let RawStatement::Call(call) = &mut st.content {
                    transform_call(ctx, call)
                };
            }
        }
    }
}
