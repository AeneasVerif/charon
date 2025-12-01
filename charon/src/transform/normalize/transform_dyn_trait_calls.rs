//! Transform method calls on `&dyn Trait` to vtable function pointer calls.
//!
//! This pass converts direct method calls on trait objects into calls through vtable
//! function pointers. For example:
//!
//! ```rust,ignore
//! let x: &dyn Trait = &obj;
//! x.method(args);
//! ```
//!
//! is transformed from:
//! ```text
//! @0 := call <dyn Trait as Trait>::method(x, args)
//! ```
//! to:
//! ```text
//! @0 := (move (*@receiver.ptr_metadata).method_check)(move (@receiver), move (@args)) // Call through function pointer
//! ```

use super::super::ctx::UllbcPass;
use crate::{
    errors::Error,
    formatter::IntoFormatter,
    pretty::FmtWithCtx,
    raise_error, register_error,
    transform::{TransformCtx, ctx::UllbcStatementTransformCtx},
    ullbc_ast::*,
};

/// Transform a call to a trait method on a dyn trait object
fn transform_dyn_trait_call(
    ctx: &mut UllbcStatementTransformCtx<'_>,
    call: &mut Call,
) -> Result<(), Error> {
    let fmt_ctx = &ctx.ctx.into_fmt();

    // Detect if this call should be transformed
    let FnOperand::Regular(fn_ptr) = &call.func else {
        return Ok(()); // Not a regular function call
    };
    let FnPtrKind::Trait(trait_ref, method_name, _) = &fn_ptr.kind else {
        return Ok(()); // Not a trait method call
    };
    let TraitRefKind::Dyn = &trait_ref.kind else {
        return Ok(()); // Not a dyn trait trait call
    };
    let trait_pred = trait_ref.trait_decl_ref.clone().erase();

    // Get the type of the vtable struct.
    let vtable_decl_ref: TypeDeclRef = {
        // Get the trait declaration by its ID
        let Some(trait_decl) = ctx.ctx.translated.trait_decls.get(trait_pred.id) else {
            return Ok(()); // Unknown trait
        };
        // Get vtable ref from definition for correct ID.
        let Some(vtable_ty) = &trait_decl.vtable else {
            raise_error!(
                ctx.ctx,
                ctx.span,
                "Found a `dyn Trait` method call for non-dyn-compatible trait `{}`!",
                trait_pred.id.with_ctx(fmt_ctx)
            );
        };
        vtable_ty
            .clone()
            .substitute_with_self(&trait_pred.generics, &trait_ref.kind)
    };
    let vtable_decl_id = *vtable_decl_ref.id.as_adt().unwrap();
    let Some(vtable_decl) = ctx.ctx.translated.type_decls.get(vtable_decl_id) else {
        return Ok(()); // Missing data
    };
    if matches!(vtable_decl.kind, TypeDeclKind::Opaque) {
        return Ok(()); // Missing data
    }

    // Retreive the method field from the vtable struct definition.
    let method_field_name = format!("method_{}", method_name);
    let Some((method_field_id, method_field)) =
        vtable_decl.get_field_by_name(None, &method_field_name)
    else {
        let vtable_name = vtable_decl_ref.id.with_ctx(fmt_ctx).to_string();
        raise_error!(
            ctx.ctx,
            ctx.span,
            "Could not determine method index for {} in vtable {}",
            method_name,
            vtable_name
        );
    };
    let method_ty = method_field
        .ty
        .clone()
        .substitute(&vtable_decl_ref.generics);

    // Get the receiver (first argument).
    if call.args.is_empty() {
        raise_error!(ctx.ctx, ctx.span, "Dyn trait call has no arguments!");
    }
    let dyn_trait_place = match &call.args[0] {
        Operand::Copy(place) | Operand::Move(place) => place,
        Operand::Const(_) => {
            panic!("Unexpected constant as receiver for dyn trait method call")
        }
    };

    // Construct the `(*ptr.ptr_metadata).method_field` place.
    let vtable_ty = TyKind::Adt(vtable_decl_ref).into_ty();
    let ptr_to_vtable_ty = Ty::new(TyKind::RawPtr(vtable_ty.clone(), RefKind::Shared));
    let method_field_place = dyn_trait_place
        .clone()
        .project(ProjectionElem::PtrMetadata, ptr_to_vtable_ty)
        .project(ProjectionElem::Deref, vtable_ty)
        .project(
            ProjectionElem::Field(FieldProjKind::Adt(vtable_decl_id, None), method_field_id),
            method_ty,
        );

    // Transform the original call to use the function pointer
    call.func = FnOperand::Dynamic(Operand::Copy(method_field_place));

    Ok(())
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_function(&self, ctx: &mut TransformCtx, decl: &mut FunDecl) {
        decl.transform_ullbc_terminators(ctx, |ctx, term| {
            if let TerminatorKind::Call { call, .. } = &mut term.kind {
                let _ = transform_dyn_trait_call(ctx, call);
            }
        });
    }
}
