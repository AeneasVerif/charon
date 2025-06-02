//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

use std::panic;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::common::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::ullbc_ast::*;
use hax_frontend_exporter as hax;
use itertools::Itertools;

impl ItemTransCtx<'_, '_> {
    /// Translate a function's signature, and initialize a body translation context
    /// at the same time - the function signature gives us the list of region and
    /// type parameters, that we put in the translation context.
    pub(crate) fn translate_function_signature(
        &mut self,
        def: &hax::FullDef,
        item_meta: &ItemMeta,
    ) -> Result<FunSig, Error> {
        let span = item_meta.span;

        self.translate_def_generics(span, def)?;

        let signature = match &def.kind {
            hax::FullDefKind::Fn { sig, .. } => sig,
            hax::FullDefKind::AssocFn { sig, .. } => sig,
            hax::FullDefKind::Ctor {
                fields, output_ty, ..
            } => {
                let sig = hax::TyFnSig {
                    inputs: fields.iter().map(|field| field.ty.clone()).collect(),
                    output: output_ty.clone(),
                    c_variadic: false,
                    safety: hax::Safety::Safe,
                    abi: hax::ExternAbi::Rust,
                };
                &hax::Binder {
                    value: sig,
                    bound_vars: Default::default(),
                }
            }
            hax::FullDefKind::Const { ty, .. }
            | hax::FullDefKind::AssocConst { ty, .. }
            | hax::FullDefKind::AnonConst { ty, .. }
            | hax::FullDefKind::InlineConst { ty, .. }
            | hax::FullDefKind::PromotedConst { ty, .. }
            | hax::FullDefKind::Static { ty, .. } => {
                let sig = hax::TyFnSig {
                    inputs: vec![],
                    output: ty.clone(),
                    c_variadic: false,
                    safety: hax::Safety::Safe,
                    abi: hax::ExternAbi::Rust,
                };
                &hax::Binder {
                    value: sig,
                    bound_vars: Default::default(),
                }
            }
            _ => panic!("Unexpected definition for function: {def:?}"),
        };

        // Translate the signature
        trace!("signature of {:?}:\n{:?}", def.def_id, signature.value);
        let inputs: Vec<Ty> = signature
            .value
            .inputs
            .iter()
            .map(|ty| self.translate_ty(span, ty))
            .try_collect()?;
        let output = self.translate_ty(span, &signature.value.output)?;

        let fmt_ctx = &self.into_fmt();
        trace!(
            "# Input variables types:\n{}",
            pretty_display_list(|x| x.to_string_with_ctx(fmt_ctx), &inputs)
        );
        trace!("# Output variable type:\n{}", output.with_ctx(fmt_ctx));

        let is_unsafe = match signature.value.safety {
            hax::Safety::Unsafe => true,
            hax::Safety::Safe => false,
        };

        Ok(FunSig {
            generics: self.the_only_binder().params.clone(),
            is_unsafe,
            inputs,
            output,
        })
    }

    /// Generate a fake function body for ADT constructors.
    pub(crate) fn build_ctor_body(
        &mut self,
        span: Span,
        signature: &FunSig,
        adt_def_id: &hax::DefId,
        ctor_of: &hax::CtorOf,
        variant_id: usize,
        fields: &hax::IndexVec<hax::FieldIdx, hax::FieldDef>,
        output_ty: &hax::Ty,
    ) -> Result<Body, Error> {
        let adt_decl_id = self.register_type_decl_id(span, adt_def_id);
        let output_ty = self.translate_ty(span, output_ty)?;
        let mut locals = Locals {
            arg_count: fields.len(),
            locals: Vector::new(),
        };
        locals.new_var(None, output_ty);
        let args: Vec<_> = fields
            .iter()
            .map(|field| {
                let ty = self.translate_ty(span, &field.ty)?;
                let place = locals.new_var(None, ty);
                Ok(Operand::Move(place))
            })
            .try_collect()?;
        let variant = match ctor_of {
            hax::CtorOf::Struct => None,
            hax::CtorOf::Variant => Some(VariantId::from(variant_id)),
        };
        let st_kind = RawStatement::Assign(
            locals.return_place(),
            Rvalue::Aggregate(
                AggregateKind::Adt(
                    TypeId::Adt(adt_decl_id),
                    variant,
                    None,
                    Box::new(
                        signature
                            .generics
                            .identity_args(GenericsSource::item(adt_decl_id)),
                    ),
                ),
                args,
            ),
        );
        let statement = Statement::new(span, st_kind);
        let block = BlockData {
            statements: vec![statement],
            terminator: Terminator::new(span, RawTerminator::Return),
        };
        let body = Body::Unstructured(GExprBody {
            span,
            locals,
            comments: Default::default(),
            body: [block].into_iter().collect(),
        });
        Ok(body)
    }

    /// Auxiliary function to translate function calls and references to functions.
    /// Translate a function id applied with some substitutions.
    ///
    /// TODO: should we always erase the regions?
    pub(crate) fn translate_fn_ptr(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
        substs: &Vec<hax::GenericArg>,
        trait_refs: &Vec<hax::ImplExpr>,
        trait_info: &Option<hax::ImplExpr>,
    ) -> Result<FnPtr, Error> {
        let fun_def = self.t_ctx.hax_def(def_id)?;

        // Trait information
        trace!(
            "Trait information:\n- def_id: {:?}\n- impl source:\n{:?}",
            def_id,
            trait_info
        );
        trace!(
            "Method traits:\n- def_id: {:?}\n- traits:\n{:?}",
            def_id,
            trait_refs
        );

        // Check if the function is considered primitive: primitive
        // functions benefit from special treatment.
        let fun_id = if fun_def.diagnostic_item.as_deref() == Some("box_new") {
            // Built-in function.
            assert!(trait_info.is_none());
            FunIdOrTraitMethodRef::Fun(FunId::Builtin(BuiltinFunId::BoxNew))
        } else {
            let fun_id = self.register_fun_decl_id(span, def_id);
            // Two cases depending on whether we call a trait method or not
            match trait_info {
                // Direct function call
                None => FunIdOrTraitMethodRef::Fun(FunId::Regular(fun_id)),
                // Trait method
                Some(trait_info) => {
                    let impl_expr = self.translate_trait_impl_expr(span, trait_info)?;
                    let method_name = self.t_ctx.translate_trait_item_name(def_id)?;
                    FunIdOrTraitMethodRef::Trait(impl_expr, method_name, fun_id)
                }
            }
        };

        // Translate the type parameters
        let binder = match fun_def.kind() {
            hax::FullDefKind::Fn { sig, .. } | hax::FullDefKind::AssocFn { sig, .. } => {
                Some(sig.as_ref().rebind(()))
            }
            _ => None,
        };
        let generics = self.translate_generic_args(
            span,
            substs,
            trait_refs,
            binder,
            fun_id.generics_target(),
        )?;

        Ok(FnPtr {
            func: Box::new(fun_id),
            generics: Box::new(generics),
        })
    }
}
