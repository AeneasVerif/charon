//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

use std::panic;

use crate::translate::translate_bodies::BodyTransCtx;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::common::*;
use charon_lib::formatter::{Formatter, IntoFormatter};
use charon_lib::ids::Vector;
use charon_lib::ullbc_ast::*;
use hax_frontend_exporter as hax;
use itertools::Itertools;

impl ItemTransCtx<'_, '_> {
    pub(crate) fn get_item_kind(
        &mut self,
        span: Span,
        def: &hax::FullDef,
    ) -> Result<ItemKind, Error> {
        let assoc = match def.kind() {
            hax::FullDefKind::AssocTy {
                associated_item, ..
            }
            | hax::FullDefKind::AssocConst {
                associated_item, ..
            }
            | hax::FullDefKind::AssocFn {
                associated_item, ..
            } => associated_item,
            _ => return Ok(ItemKind::Regular),
        };
        Ok(match &assoc.container {
            // E.g.:
            // ```
            // impl<T> List<T> {
            //   fn new() -> Self { ... } <- inherent method
            // }
            // ```
            hax::AssocItemContainer::InherentImplContainer { .. } => ItemKind::Regular,
            // E.g.:
            // ```
            // impl Foo for Bar {
            //   fn baz(...) { ... } // <- implementation of a trait method
            // }
            // ```
            hax::AssocItemContainer::TraitImplContainer {
                impl_id,
                impl_generics,
                impl_required_impl_exprs,
                implemented_trait_ref,
                implemented_trait_item,
                overrides_default,
                ..
            } => {
                let impl_id = self.register_trait_impl_id(span, impl_id);
                let impl_ref = TraitImplRef {
                    impl_id,
                    generics: self.translate_generic_args(
                        span,
                        impl_generics,
                        impl_required_impl_exprs,
                        None,
                        GenericsSource::item(impl_id),
                    )?,
                };
                let trait_ref = self.translate_trait_ref(span, implemented_trait_ref)?;
                if matches!(def.kind(), hax::FullDefKind::AssocFn { .. }) {
                    // Ensure we translate the corresponding decl signature.
                    // FIXME(self_clause): also ensure we translate associated globals
                    // consistently; to do once we have clearer `Self` clause handling.
                    let _ = self.register_fun_decl_id(span, implemented_trait_item);
                }
                ItemKind::TraitImpl {
                    impl_ref,
                    trait_ref,
                    item_name: TraitItemName(assoc.name.clone()),
                    reuses_default: !overrides_default,
                }
            }
            // This method is the *declaration* of a trait item
            // E.g.:
            // ```
            // trait Foo {
            //   fn baz(...); // <- declaration of a trait method
            // }
            // ```
            hax::AssocItemContainer::TraitContainer { trait_ref, .. } => {
                // The trait id should be Some(...): trait markers (that we may eliminate)
                // don't have associated items.
                let trait_ref = self.translate_trait_ref(span, trait_ref)?;
                let item_name = TraitItemName(assoc.name.clone());
                ItemKind::TraitDecl {
                    trait_ref,
                    item_name,
                    has_default: assoc.has_value,
                }
            }
        })
    }

    /// Translate a function's signature, and initialize a body translation context
    /// at the same time - the function signature gives us the list of region and
    /// type parameters, that we put in the translation context.
    fn translate_function_signature(
        &mut self,
        def: &hax::FullDef,
        item_meta: &ItemMeta,
    ) -> Result<FunSig, Error> {
        let span = item_meta.span;

        self.translate_def_generics(span, def)?;

        let signature = match &def.kind {
            hax::FullDefKind::Closure { args, .. } => &args.tupled_sig,
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
        let mut inputs: Vec<Ty> = signature
            .value
            .inputs
            .iter()
            .map(|ty| self.translate_ty(span, ty))
            .try_collect()?;
        let output = self.translate_ty(span, &signature.value.output)?;

        let fmt_ctx = self.into_fmt();
        trace!(
            "# Input variables types:\n{}",
            pretty_display_list(|x| fmt_ctx.format_object(x), &inputs)
        );
        trace!(
            "# Output variable type:\n{}",
            fmt_ctx.format_object(&output)
        );

        let is_unsafe = match signature.value.safety {
            hax::Safety::Unsafe => true,
            hax::Safety::Safe => false,
        };

        let closure_info = match &def.kind {
            hax::FullDefKind::Closure { args, .. } => {
                let kind = match args.kind {
                    hax::ClosureKind::Fn => ClosureKind::Fn,
                    hax::ClosureKind::FnMut => ClosureKind::FnMut,
                    hax::ClosureKind::FnOnce => ClosureKind::FnOnce,
                };

                assert_eq!(inputs.len(), 1);
                let tuple_arg = inputs.pop().unwrap();

                let state: Vector<TypeVarId, Ty> = args
                    .upvar_tys
                    .iter()
                    .map(|ty| self.translate_ty(span, &ty))
                    .try_collect()?;
                // Add the state of the closure as first parameter.
                let state_ty = {
                    // Group the state types into a tuple
                    let state_ty =
                        TyKind::Adt(TypeId::Tuple, GenericArgs::new_for_builtin(state.clone()))
                            .into_ty();
                    // Depending on the kind of the closure, add a reference
                    match &kind {
                        ClosureKind::FnOnce => state_ty,
                        ClosureKind::Fn | ClosureKind::FnMut => {
                            let rid = self
                                .innermost_generics_mut()
                                .regions
                                .push_with(|index| RegionVar { index, name: None });
                            let r = Region::Var(DeBruijnVar::new_at_zero(rid));
                            let mutability = if kind == ClosureKind::Fn {
                                RefKind::Shared
                            } else {
                                RefKind::Mut
                            };
                            TyKind::Ref(r, state_ty, mutability).into_ty()
                        }
                    }
                };
                inputs.push(state_ty);

                // Unpack the tupled arguments to match the body locals.
                let TyKind::Adt(TypeId::Tuple, tuple_args) = tuple_arg.kind() else {
                    raise_error!(self, span, "Closure argument is not a tuple")
                };
                inputs.extend(tuple_args.types.iter().cloned());

                Some(ClosureInfo { kind, state })
            }
            _ => None,
        };

        Ok(FunSig {
            generics: self.the_only_binder().params.clone(),
            is_unsafe,
            is_closure: matches!(&def.kind, hax::FullDefKind::Closure { .. }),
            closure_info,
            inputs,
            output,
        })
    }

    /// Generate a fake function body for ADT constructors.
    fn build_ctor_body(
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
                    signature
                        .generics
                        .identity_args(GenericsSource::item(adt_decl_id)),
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
            func: fun_id,
            generics,
        })
    }

    /// Translate one function.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_function(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<FunDecl, Error> {
        trace!("About to translate function:\n{:?}", def.def_id);
        let span = item_meta.span;

        // Translate the function signature
        trace!("Translating function signature");
        let signature = self.translate_function_signature(def, &item_meta)?;

        // Check whether this function is a method declaration for a trait definition.
        // If this is the case, it shouldn't contain a body.
        let kind = self.get_item_kind(span, def)?;
        let is_trait_method_decl_without_default = match &kind {
            ItemKind::Regular | ItemKind::TraitImpl { .. } => false,
            ItemKind::TraitDecl { has_default, .. } => !has_default,
        };

        let is_global_initializer = matches!(
            def.kind(),
            hax::FullDefKind::Const { .. }
                | hax::FullDefKind::AssocConst { .. }
                | hax::FullDefKind::AnonConst { .. }
                | hax::FullDefKind::InlineConst { .. }
                | hax::FullDefKind::PromotedConst { .. }
                | hax::FullDefKind::Static { .. }
        );
        let is_global_initializer =
            is_global_initializer.then(|| self.register_global_decl_id(span, &def.def_id));

        let body_id = if item_meta.opacity.with_private_contents().is_opaque()
            || is_trait_method_decl_without_default
        {
            Err(Opaque)
        } else if let hax::FullDefKind::Ctor {
            adt_def_id,
            ctor_of,
            variant_id,
            fields,
            output_ty,
            ..
        } = def.kind()
        {
            let body = self.build_ctor_body(
                span,
                &signature,
                adt_def_id,
                ctor_of,
                *variant_id,
                fields,
                output_ty,
            )?;
            Ok(body)
        } else {
            // Translate the body. This doesn't store anything if we can't/decide not to translate
            // this body.
            let mut bt_ctx = BodyTransCtx::new(&mut self);
            match bt_ctx.translate_body(item_meta.span, def) {
                Ok(Ok(body)) => Ok(body),
                // Opaque declaration
                Ok(Err(Opaque)) => Err(Opaque),
                // Translation error.
                // FIXME: handle error cases more explicitly.
                Err(_) => Err(Opaque),
            }
        };
        Ok(FunDecl {
            def_id,
            item_meta,
            signature,
            kind,
            is_global_initializer,
            body: body_id,
        })
    }

    /// Translate one global.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_global(
        mut self,
        def_id: GlobalDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<GlobalDecl, Error> {
        trace!("About to translate global:\n{:?}", def.def_id);
        let span = item_meta.span;

        // Translate the generics and predicates - globals *can* have generics
        // Ex.:
        // ```
        // impl<const N : usize> Foo<N> {
        //   const LEN : usize = N;
        // }
        // ```
        self.translate_def_generics(span, def)?;

        // Retrieve the kind
        let item_kind = self.get_item_kind(span, def)?;

        trace!("Translating global type");
        let ty = match &def.kind {
            hax::FullDefKind::Const { ty, .. }
            | hax::FullDefKind::AssocConst { ty, .. }
            | hax::FullDefKind::AnonConst { ty, .. }
            | hax::FullDefKind::InlineConst { ty, .. }
            | hax::FullDefKind::PromotedConst { ty, .. }
            | hax::FullDefKind::Static { ty, .. } => ty,
            _ => panic!("Unexpected def for constant: {def:?}"),
        };
        let ty = self.translate_ty(span, ty)?;

        let global_kind = match &def.kind {
            hax::FullDefKind::Static { .. } => GlobalKind::Static,
            hax::FullDefKind::Const { .. } | hax::FullDefKind::AssocConst { .. } => {
                GlobalKind::NamedConst
            }
            hax::FullDefKind::AnonConst { .. }
            | hax::FullDefKind::InlineConst { .. }
            | hax::FullDefKind::PromotedConst { .. } => GlobalKind::AnonConst,
            _ => panic!("Unexpected def for constant: {def:?}"),
        };

        let initializer = self.register_fun_decl_id(span, &def.def_id);

        Ok(GlobalDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            ty,
            kind: item_kind,
            global_kind,
            init: initializer,
        })
    }
}
