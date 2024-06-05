use crate::{
    gast::TraitInstanceId,
    llbc_ast::{Call, FnOperand, FunId, FunIdOrTraitMethodRef},
    transform::TransformCtx,
    ullbc_ast::{ExprBody, RawTerminator},
};

use super::ctx::UllbcPass;

fn transform_call(ctx: &mut TransformCtx, call: &mut Call) {
    // We find calls to a trait method where the impl is known; otherwise we return.
    let FnOperand::Regular(fn_ptr) = &mut call.func else {
        return;
    };
    let FunIdOrTraitMethodRef::Trait(trait_ref, name, _) = &fn_ptr.func else {
        return;
    };
    let TraitInstanceId::TraitImpl(impl_id) = &trait_ref.trait_id else {
        return;
    };
    let trait_impl = &ctx.translated.trait_impls[*impl_id];
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
    let trait_generics = &trait_ref.generics;
    // Move the trait generics to the function call.
    // FIXME: make a better API than `concat`.
    fn_ptr.generics = trait_generics.clone().concat(fn_generics.clone());
    // Set the call operation to use the function directly.
    fn_ptr.func = FunIdOrTraitMethodRef::Fun(FunId::Regular(*fun_decl_id));
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        for block in b.body.iter_mut() {
            if let RawTerminator::Call { call, .. } = &mut block.terminator.content {
                transform_call(ctx, call)
            };
        }
    }
}
