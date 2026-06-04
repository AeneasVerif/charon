use derive_generic_visitor::Visitor;

use crate::transform::ctx::UllbcPass;
use crate::{transform::TransformCtx, ullbc_ast::*};

#[derive(Visitor)]
struct NormalizeFnPtr<'a> {
    ctx: &'a TransformCtx,
}

impl VisitAstMut for NormalizeFnPtr<'_> {
    fn enter_fn_ptr(&mut self, fn_ptr: &mut FnPtr) {
        if let Some(new_fn_ptr) = normalize_default_method_call_on_known_impl(self.ctx, fn_ptr)
            .or_else(|| normalize_method_call_on_known_impl(self.ctx, fn_ptr))
        {
            *fn_ptr = new_fn_ptr;
        }
    }
}

/// Transform `Trait::default_method<X>[impl_trait_for_X]` to a direct method call.
fn normalize_default_method_call_on_known_impl(
    ctx: &TransformCtx,
    fn_ptr: &FnPtr,
) -> Option<FnPtr> {
    let fun_id = fn_ptr.kind.as_ref().as_fun()?.as_regular()?;
    let fun_decl = ctx.translated.fun_decls.get(*fun_id)?;
    let ItemSource::TraitDecl {
        trait_ref,
        item_id: AssocItemId::Method(method_id),
        has_default: true,
    } = &fun_decl.src
    else {
        return None;
    };
    // If the first trait proof (for the self clause) is a known impl.
    let impl_ref = fn_ptr
        .generics
        .trait_refs
        .get(TraitClauseId::ZERO)
        .as_ref()?
        .kind
        .as_trait_impl()?;
    let method_generics = {
        let generics = &fn_ptr.generics;
        let trait_generics = trait_ref.generics.as_ref();
        GenericArgs {
            regions: generics
                .regions
                .clone()
                .split_off(trait_generics.regions.len()),
            types: generics.types.clone().split_off(trait_generics.types.len()),
            const_generics: generics
                .const_generics
                .clone()
                .split_off(trait_generics.const_generics.len()),
            // The `+ 1` is for the self clause.
            trait_refs: generics
                .trait_refs
                .clone()
                .split_off(trait_generics.trait_refs.len() + 1),
        }
    };
    normalize_method_call(ctx, impl_ref, method_id, &method_generics)
}

/// Transform `impl_trait_for_X::method` to a direct method call.
fn normalize_method_call_on_known_impl(ctx: &TransformCtx, fn_ptr: &FnPtr) -> Option<FnPtr> {
    let FnPtrKind::Trait(trait_ref, method_id, _) = fn_ptr.kind.as_ref() else {
        return None;
    };
    let TraitRefKind::TraitImpl(impl_ref) = &trait_ref.kind else {
        return None;
    };
    normalize_method_call(ctx, impl_ref, method_id, &fn_ptr.generics)
}

fn normalize_method_call(
    ctx: &TransformCtx,
    impl_ref: &TraitImplRef,
    method_id: &TraitMethodId,
    method_generics: &GenericArgs,
) -> Option<FnPtr> {
    let trait_impl = &ctx.translated.trait_impls.get(impl_ref.id)?;
    // Find the function declaration corresponding to this impl.
    let bound_fn = trait_impl.methods.get(*method_id)?;
    if !method_generics.matches(&bound_fn.params) {
        return None;
    }

    // Make the two levels of binding explicit: outer binder for the impl block, inner binder for
    // the method.
    let fn_ref: Binder<Binder<FunDeclRef>> = Binder::new(
        BinderKind::Other,
        trait_impl.generics.clone(),
        bound_fn.clone(),
    );
    // Substitute the appropriate generics into the function call.
    let fn_ref = fn_ref.apply(&impl_ref.generics).apply(method_generics);
    Some(FnPtr::new(
        FnPtrKind::Fun(FunId::Regular(fn_ref.id)),
        fn_ref.generics,
    ))
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_item(&self, ctx: &mut TransformCtx, mut item: ItemRefMut<'_>) {
        let _ = item.drive_mut(&mut NormalizeFnPtr { ctx });
    }
}
