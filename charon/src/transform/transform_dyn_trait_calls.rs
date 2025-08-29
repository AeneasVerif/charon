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
//! vtable@9 := ptr_metadata(move (@receiver))              // Extract vtable pointer
//! method_ptr@8 := copy (((*vtable@9).method_check))       // Get method from vtable
//! @0 := (move method_ptr@8)(move (@receiver), move (@args)) // Call through function pointer
//! ```

use super::ctx::UllbcPass;
use crate::{
    errors::Error, formatter::IntoFormatter, pretty::FmtWithCtx, raise_error, register_error,
    transform::TransformCtx, ullbc_ast::*,
};

/// Transformer for dynamic trait calls that holds common state and provides methods
/// for the transformation operations.
struct DynTraitCallTransformer<'a> {
    ctx: &'a TransformCtx,
    span: Span,
    statements: &'a mut Vec<Statement>,
    locals: &'a mut Locals,
}

impl<'a> DynTraitCallTransformer<'a> {
    fn new(
        ctx: &'a TransformCtx,
        span: Span,
        statements: &'a mut Vec<Statement>,
        locals: &'a mut Locals,
    ) -> Self {
        Self {
            ctx,
            span,
            statements,
            locals,
        }
    }

    /// Detect if a call should be transformed to use vtable dispatch
    /// Returns the trait reference and method name for the dyn trait call if found
    fn detect_dyn_trait_call(&self, call: &Call) -> Option<(TraitRef, TraitItemName)> {
        // Check if this is a regular function call
        let FnOperand::Regular(fn_ptr) = &call.func else {
            return None; // Not a regular function call
        };

        let FunIdOrTraitMethodRef::Trait(trait_ref, method_name, _) = &fn_ptr.func else {
            return None; // Not a trait method call
        };

        match &trait_ref.kind {
            TraitRefKind::Dyn => Some((trait_ref.clone(), method_name.clone())),
            _ => None,
        }
    }

    /// Get the vtable declaration reference with current generics applied.
    /// Matches associated types from the vtable's generics with the dyn trait's constraints.
    ///
    /// Rustc guarantees all associated types are specified in a `dyn Trait` type.
    fn get_vtable_ref(&self, trait_ref: &TraitRef, dyn_self_ty: &Ty) -> Result<TypeDeclRef, Error> {
        // Get vtable_ref's ID with trait-ref's generics from dyn-self applied.
        // Add associated types in correct order following the vtable's generics.

        // 0. Prepare trait name for debug/error messages
        let trait_name = trait_ref
            .trait_decl_ref
            .skip_binder
            .id
            .with_ctx(&self.ctx.into_fmt())
            .to_string();

        // 1. Get vtable ref from trait declaration
        //    Provides: 1) final return ID, 2) correct order of associated types
        // Firstly, get the trait declaration for the vtable ref it stores.
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
        // Generics in vtable ref are placeholders but provide correct order of the associated types.
        let Some(vtable_ref) = &trait_decl.vtable else {
            raise_error!(
                self.ctx,
                self.span,
                "Vtable for trait {} is None, meaning the trait is non-dyn-compatible!",
                trait_name
            );
        };

        // 2. Get correct generics for vtable ref from `dyn_self_ty`
        //    The binder contains all target generics info.
        let TyKind::DynTrait(DynPredicate { binder }) = dyn_self_ty.kind() else {
            raise_error!(
                self.ctx,
                self.span,
                "Expected dyn trait type for dyn method calling receiver, found {}",
                dyn_self_ty.with_ctx(&self.ctx.into_fmt())
            );
        };

        // 3. Prepare "basic part" of generics from trait ref (without associated types)
        // The trait ref `dyn Trait<_dyn, Arg1, ..., ArgN>`, no associated types.
        // First trait clause is the target one for vtable, guaranteed by `DynPredicate`.
        let trait_ref = binder.params.trait_clauses[0].trait_.clone().erase();
        // Type vars (except `_dyn`) are one level deeper, move out after removing `_dyn`.
        trace!(
            "Getting vtable ref with trait-decl-ref {}.",
            trait_ref.with_ctx(&self.ctx.into_fmt())
        );
        let mut generics = trait_ref.generics.clone();
        // Remove the first `_dyn` type argument
        generics.types.remove_and_shift_ids(TypeVarId::ZERO);
        // Move out of predicate binder for `_dyn`
        generics = generics.move_from_under_binder().unwrap();

        // 4. Prepare associated types part in same order as vtable's generics
        // Utilise the vtable ref form:
        // `{vtable}<TraitArg1, ..., SuperTrait::Assoc1, ..., Self::AssocN>`
        //
        // Use trait ID + assoc name (`Trait::AssocTy`) to uniquely identify
        let assoc_tys = vtable_ref
            .generics
            .types
            .iter()
            .filter_map(|ty| {
                if let TyKind::TraitType(tref, name) = &ty.kind() {
                    Some((tref.trait_decl_ref.skip_binder.id, name.clone()))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        // Find correct type argument from dyn trait's constraints for each assoc type.
        for (trait_id, assoc_name) in assoc_tys {
            // Find it
            let Some(assoc_ty) = binder.params.trait_type_constraints.iter().find_map(|c| {
                let c = c.clone().erase();
                if c.trait_ref.trait_decl_ref.skip_binder.id == trait_id
                    && c.type_name == assoc_name
                {
                    // Move potentially bounded type out of `_dyn` binder
                    Some(c.ty.clone().move_from_under_binder().unwrap())
                } else {
                    None
                }
            }) else {
                raise_error!(
                    self.ctx,
                    self.span,
                    "Could not find associated type {}::{} for vtable of trait {} in dyn Trait type: {}",
                    trait_id.with_ctx(&self.ctx.into_fmt()),
                    assoc_name,
                    trait_name,
                    dyn_self_ty.with_ctx(&self.ctx.into_fmt())
                );
            };
            // Push it
            generics.types.push(assoc_ty);
        }

        // 5. Return vtable ref's ID with correct generics
        Ok(TypeDeclRef {
            id: vtable_ref.id,
            generics,
        })
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
    /// TODO: use the vtable ref to create the correct types
    fn create_vtable_locals(
        &mut self,
        vtable_ref: &TypeDeclRef,
        method_ptr_ty: &Ty,
    ) -> (Place, Place) {
        // Create vtable type - for now use a raw pointer as placeholder
        // In complete implementation this would be the actual vtable struct type
        let vtable_ty = Ty::new(TyKind::RawPtr(
            Ty::new(TyKind::Adt(vtable_ref.clone())),
            RefKind::Shared,
        ));

        let vtable_place = self.locals.new_var(None, vtable_ty);
        // push the storage-live statements for the new locals
        self.statements.push(Statement {
            span: self.span,
            content: RawStatement::StorageLive(vtable_place.as_local().unwrap()),
            comments_before: vec![],
        });

        let method_ptr_place = self.locals.new_var(None, method_ptr_ty.clone());
        self.statements.push(Statement {
            span: self.span,
            content: RawStatement::StorageLive(method_ptr_place.as_local().unwrap()),
            comments_before: vec![],
        });

        (vtable_place, method_ptr_place)
    }

    /// Generate the statement that extracts the vtable pointer from the dyn trait object
    fn generate_vtable_extraction(
        &self,
        vtable_place: &Place,
        dyn_trait_operand: &Operand,
    ) -> Statement {
        Statement {
            span: self.span,
            content: RawStatement::Assign(
                vtable_place.clone(),
                Rvalue::UnaryOp(UnOp::PtrMetadata, dyn_trait_operand.clone()),
            ),
            comments_before: vec!["Extract vtable pointer from dyn trait object".to_string()],
        }
    }

    /// Generate the statement that extracts the method pointer from the vtable
    fn generate_method_pointer_extraction(
        &self,
        method_ptr_place: &Place,
        vtable_place: &Place,
        field_id: FieldId,
    ) -> Statement {
        // Create vtable dereference: *vtable
        let vtable_deref_place = Place {
            kind: PlaceKind::Projection(Box::new(vtable_place.clone()), ProjectionElem::Deref),
            ty: Ty::mk_unit(), // placeholder type
        };

        // Create method field projection: (*vtable).method_field
        let method_field_place = Place {
            kind: PlaceKind::Projection(
                Box::new(vtable_deref_place),
                ProjectionElem::Field(
                    FieldProjKind::Adt(TypeDeclId::new(0), None), // Placeholder vtable type ID
                    field_id,
                ),
            ),
            ty: method_ptr_place.ty.clone(),
        };

        Statement {
            span: self.span,
            content: RawStatement::Assign(
                method_ptr_place.clone(),
                Rvalue::Use(Operand::Copy(method_field_place)),
            ),
            comments_before: vec!["Get method pointer from vtable".to_string()],
        }
    }

    /// The receiver type can be one of the following (as per Rustc):
    /// - `&[mut] dyn Trait`
    /// - `*[mut] dyn Trait`
    /// - `Box<dyn Trait>`
    /// - `Rc<dyn Trait>`
    /// - `Arc<dyn Trait>`
    /// - `Pin<T>` where `T` is one of the above
    ///
    /// See: https://doc.rust-lang.org/reference/items/traits.html#dyn-compatibility
    /// for more details.
    ///
    /// This function gets the internal `dyn Trait` out
    fn unpack_dyn_trait_ty(&self, ty: &Ty) -> Result<Ty, Error> {
        match ty.kind() {
            TyKind::Ref(_, inner_ty, _) => self.unpack_dyn_trait_ty(inner_ty),
            TyKind::RawPtr(inner_ty, _) => self.unpack_dyn_trait_ty(inner_ty),
            TyKind::Adt(type_decl_ref) => {
                let generics = &type_decl_ref.generics;
                if !generics.types.is_empty() {
                    let first_arg = generics.types.get(TypeVarId::new(0)).unwrap();
                    self.unpack_dyn_trait_ty(first_arg)
                } else {
                    raise_error!(
                        self.ctx,
                        self.span,
                        "Expected dyn trait type for dyn method calling receiver, found {}",
                        ty.with_ctx(&self.ctx.into_fmt())
                    );
                }
            }
            TyKind::DynTrait(_) => Ok(ty.clone()),
            _ => raise_error!(
                self.ctx,
                self.span,
                "Expected dyn trait type for dyn method calling receiver, found {}",
                ty.with_ctx(&self.ctx.into_fmt())
            ),
        }
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

        // 2. Get the dyn trait argument
        if call.args.is_empty() {
            raise_error!(self.ctx, self.span, "Dyn trait call has no arguments!");
        }
        let dyn_trait_operand = &call.args[0].clone();
        let receiver_ty = dyn_trait_operand.ty().clone();
        let dyn_self_ty = self.unpack_dyn_trait_ty(&receiver_ty)?;

        let vtable_ref = self.get_vtable_ref(&trait_ref, &dyn_self_ty)?;

        // 3. Get the correct field index & type for the method
        let field_id = self.get_method_field_id(&vtable_ref, &method_name)?;
        let field_ty = self.fun_ty_from_call(call)?;

        // 4. Create local variables for vtable and method pointer
        let (vtable_place, method_ptr_place) = self.create_vtable_locals(&vtable_ref, &field_ty);

        // Extract vtable pointer
        self.statements
            .push(self.generate_vtable_extraction(&vtable_place, &dyn_trait_operand));

        // Extract method pointer from vtable
        self.statements
            .push(self.generate_method_pointer_extraction(
                &method_ptr_place,
                &vtable_place,
                field_id,
            ));

        // 6. Transform the original call to use the function pointer
        call.func = FnOperand::Move(method_ptr_place);

        trace!(
            "Generated {} new statements for vtable dispatch",
            self.statements.len()
        );
        Ok(Some(()))
    }
}

pub struct Transform;

impl UllbcPass for Transform {
    fn transform_body(&self, ctx: &mut TransformCtx, body: &mut ExprBody) {
        trace!(
            "TransformDynTraitCalls: Processing body with {} blocks",
            body.body.iter().count()
        );

        for (block_id, block) in body.body.iter_mut().enumerate() {
            let block_id = BlockId::new(block_id);

            // Check terminator for calls
            if let RawTerminator::Call { call, .. } = &mut block.terminator.content {
                trace!("Found call in block {}: {:?}", block_id, call.func);
                let span = block.terminator.span;
                let mut transformer = DynTraitCallTransformer::new(
                    ctx,
                    span,
                    &mut block.statements,
                    &mut body.locals,
                );
                match transformer.transform_dyn_trait_call(call) {
                    Ok(Some(_)) => {
                        trace!("Successfully transformed dynamic trait call");
                    }
                    Ok(None) => {
                        trace!("No transformation needed for this call");
                    }
                    Err(e) => {
                        register_error!(
                            ctx,
                            span,
                            "Failed to transform dynamic trait call: {:?}",
                            e
                        );
                    }
                }
            }
        }
    }

    fn name(&self) -> &str {
        "TransformDynTraitCalls"
    }
}
