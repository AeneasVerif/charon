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
//! @0 := call TraitMethod::method(x, args)
//! ```
//!
//! to:
//! ```text
//! vtable@9 := (@receiver).ptr_metadata                      // Extract vtable pointer
//! method_ptr@8 := copy (((*vtable@9).method_check))         // Get method from vtable
//! @0 := (move method_ptr@8)(move (@receiver), move (@args)) // Call through function pointer
//! ```

use super::super::ctx::UllbcPass;
use crate::{
    errors::Error,
    formatter::IntoFormatter,
    pretty::FmtWithCtx,
    raise_error, register_error,
    transform::{
        TransformCtx,
        ctx::{BodyTransformCtx, UllbcStatementTransformCtx},
    },
    ullbc_ast::*,
};

impl<'a> UllbcStatementTransformCtx<'a> {
    /// Detect if a call should be transformed to use vtable dispatch
    /// Returns the trait reference and method name for the dyn trait call if found
    fn detect_dyn_trait_call<'b>(
        &self,
        call: &'b Call,
    ) -> Option<(&'b TraitRef, &'b TraitItemName)> {
        // Check if this is a regular function call
        let FnOperand::Regular(fn_ptr) = &call.func else {
            return None; // Not a regular function call
        };

        let FnPtrKind::Trait(trait_ref, method_name, _) = &fn_ptr.kind else {
            return None; // Not a trait method call
        };

        match &trait_ref.kind {
            TraitRefKind::Dyn => Some((trait_ref, method_name)),
            _ => None,
        }
    }

    /// Get the vtable declaration reference with current generics applied.
    /// The associated types are resolved in the next pass.
    fn get_vtable_ref(&self, trait_ref: &TraitRef) -> Result<TypeDeclRef, Error> {
        // Prepare trait name for debug/error messages
        let trait_name = trait_ref
            .trait_decl_ref
            .skip_binder
            .id
            .with_ctx(&self.ctx.into_fmt())
            .to_string();

        // Get the trait declaration by its ID
        let Some(trait_decl) = self
            .ctx
            .translated
            .trait_decls
            .get(trait_ref.trait_decl_ref.skip_binder.id)
        else {
            raise_error!(
                self.ctx,
                self.span,
                "Trait definition for {} not found!",
                trait_name
            );
        };

        // Get vtable ref from definition for correct ID.
        let Some(vtable_ref) = &trait_decl.vtable else {
            raise_error!(
                self.ctx,
                self.span,
                "Vtable for trait {} is None, meaning the trait is non-dyn-compatible!",
                trait_name
            );
        };

        let trait_pred = trait_ref.trait_decl_ref.clone().erase();
        let vtable_ref = vtable_ref
            .clone()
            .substitute_with_self(&trait_pred.generics, &trait_ref.kind);
        Ok(vtable_ref)
    }

    /// Get the correct field index for a method in the vtable struct.
    fn get_method_field_id(
        &self,
        vtable_ref: &TypeDeclRef,
        method_name: &TraitItemName,
    ) -> Result<FieldId, Error> {
        let vtable_name = vtable_ref.id.with_ctx(&self.ctx.into_fmt()).to_string();

        let TypeId::Adt(vtable_id) = vtable_ref.id else {
            raise_error!(
                self.ctx,
                self.span,
                "Vtable reference {} is not an ADT type!",
                vtable_name
            );
        };

        // Get the vtable struct declaration by its ID
        let Some(TypeDecl {
            kind: TypeDeclKind::Struct(fields),
            ..
        }) = self.ctx.translated.type_decls.get(vtable_id)
        else {
            raise_error!(
                self.ctx,
                self.span,
                "Definition of vtable struct {} is not found!",
                vtable_name
            );
        };

        // Find the index from the fields
        for (index, field) in fields.iter().enumerate() {
            if format!("method_{}", method_name) == *field.name.as_ref().unwrap() {
                return Ok(FieldId::new(index));
            }
        }

        // If we reach here, the method was not found in the vtable, which is an error
        raise_error!(
            self.ctx,
            self.span,
            "Could not determine method index for {} in vtable {}",
            method_name,
            vtable_name
        );
    }

    /// Create local variables needed for vtable dispatch
    fn create_vtable_locals(
        &mut self,
        vtable_ref: &TypeDeclRef,
        method_ptr_ty: &Ty,
    ) -> (Place, Place) {
        // A raw pointer to the vtable struct type
        let vtable_ty = Ty::new(TyKind::RawPtr(
            Ty::new(TyKind::Adt(vtable_ref.clone())),
            RefKind::Shared,
        ));

        let vtable_place = self.fresh_var(None, vtable_ty);
        let method_ptr_place = self.fresh_var(None, method_ptr_ty.clone());

        (vtable_place, method_ptr_place)
    }

    /// Generate the statement that extracts the vtable pointer from the dyn trait object
    fn insert_vtable_extraction(&mut self, vtable_place: &Place, dyn_trait_place: &Place) {
        let ptr_metadata_place = dyn_trait_place
            .clone()
            .project(ProjectionElem::PtrMetadata, vtable_place.ty().clone());
        self.insert_assn_stmt(
            vtable_place.clone(),
            Rvalue::Use(Operand::Copy(ptr_metadata_place)),
        );
    }

    /// Generate the statement that extracts the method pointer from the vtable
    fn insert_method_pointer_extraction(
        &mut self,
        method_ptr_place: &Place,
        vtable_place: &Place,
        field_id: FieldId,
    ) {
        let vtable_deref_ty = match vtable_place.ty().kind() {
            TyKind::RawPtr(inner_ty, _) | TyKind::Ref(_, inner_ty, _) => inner_ty.clone(),
            _ => panic!(
                "Expected pointer / reference type for the vtable place, got: {}",
                vtable_place.ty().with_ctx(&self.ctx.into_fmt())
            ),
        };

        let vtable_def_id = match vtable_deref_ty.kind() {
            TyKind::Adt(adt_ref) => match adt_ref.id {
                TypeId::Adt(def_id) => def_id,
                _ => panic!(
                    "Expected ADT type ID for the vtable struct, got: {}",
                    adt_ref.id.with_ctx(&self.ctx.into_fmt())
                ),
            },
            _ => panic!(
                "Expected ADT type for the vtable struct, got: {}",
                vtable_deref_ty.with_ctx(&self.ctx.into_fmt())
            ),
        };

        // Create vtable dereference: *vtable
        let vtable_deref_place = Place {
            kind: PlaceKind::Projection(Box::new(vtable_place.clone()), ProjectionElem::Deref),
            ty: vtable_deref_ty,
        };

        // Create method field projection: (*vtable).method_field
        let method_field_place = Place {
            kind: PlaceKind::Projection(
                Box::new(vtable_deref_place),
                ProjectionElem::Field(FieldProjKind::Adt(vtable_def_id, None), field_id),
            ),
            ty: method_ptr_place.ty.clone(),
        };

        self.insert_assn_stmt(
            method_ptr_place.clone(),
            Rvalue::Use(Operand::Copy(method_field_place)),
        );
    }

    fn fun_ty_from_call(&self, call: &Call) -> Result<Ty, Error> {
        let input = call.args.iter().map(|arg| arg.ty().clone()).collect();
        let output = call.dest.ty().clone();
        Ok(Ty::new(TyKind::FnPtr(RegionBinder::empty((input, output)))))
    }

    /// Transform a call to a trait method on a dyn trait object
    fn transform_dyn_trait_call(&mut self, call: &mut Call) -> Result<Option<()>, Error> {
        // 1. Detect if this call should be transformed
        let (trait_ref, method_name) = match self.detect_dyn_trait_call(call) {
            Some(info) => info,
            None => return Ok(None),
        };

        // 2. Get the receiver (first argument)
        if call.args.is_empty() {
            raise_error!(self.ctx, self.span, "Dyn trait call has no arguments!");
        }
        let dyn_trait_place = match &call.args[0] {
            Operand::Copy(place) => place,
            Operand::Move(place) => place,
            Operand::Const(_) => {
                panic!("Unexpected constant as receiver for dyn trait method call");
            }
        };

        let vtable_ref = self.get_vtable_ref(&trait_ref)?;

        // 3. Get the correct field index & type for the method
        let field_id = self.get_method_field_id(&vtable_ref, &method_name)?;
        let field_ty = self.fun_ty_from_call(call)?;

        // 4. Create local variables for vtable and method pointer
        let (vtable_place, method_ptr_place) = self.create_vtable_locals(&vtable_ref, &field_ty);

        // 5. Insert statement to extract vtable pointer from the dyn trait object
        self.insert_vtable_extraction(&vtable_place, &dyn_trait_place);

        // 6. Insert statement to extract method pointer from vtable
        self.insert_method_pointer_extraction(&method_ptr_place, &vtable_place, field_id);

        // 7. Transform the original call to use the function pointer
        call.func = FnOperand::Move(method_ptr_place);

        Ok(Some(()))
    }
}

pub struct Transform;

impl UllbcPass for Transform {
    fn transform_function(&self, ctx: &mut TransformCtx, decl: &mut FunDecl) {
        decl.transform_ullbc_terminators(ctx, |ctx, term| {
            if let TerminatorKind::Call { call, .. } = &mut term.kind {
                let _ = ctx.transform_dyn_trait_call(call);
            }
        });
    }
}
