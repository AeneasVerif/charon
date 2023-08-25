#![allow(dead_code)]
use crate::gast::{GenericArgs, ImplTraitRef, TraitMethodName};
use crate::names_utils;
use crate::translate_ctx::*;
use crate::ullbc_ast as ast;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// Remark: this **doesn't** register the def id (on purpose)
    pub(crate) fn translate_trait_method_name(&mut self, rust_id: DefId) -> TraitMethodName {
        // Translate the name
        let name = names_utils::item_def_id_to_name(self.tcx, rust_id);
        TraitMethodName(name.name.last().unwrap().as_ident().clone())
    }

    pub(crate) fn translate_trait_decl(&mut self, rust_id: DefId) {
        let def_id = self.translate_trait_decl_id(rust_id);
        let tcx = self.tcx;
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        let name = names_utils::extended_def_id_to_name(&rust_id.sinto(&bt_ctx.hax_state));

        // Translate the generic
        let _substs = bt_ctx.translate_generics(rust_id);

        // Translate the predicates
        bt_ctx.translate_predicates_of(rust_id);

        trace!("- trait id: {:?}\n- trait name: {:?}", rust_id, name);
        trace!("Trait predicates: {:?}", tcx.predicates_of(rust_id));

        // Explore the associated items
        // We do something subtle here: TODO
        let tcx = bt_ctx.t_ctx.tcx;
        let associated_items = tcx.associated_items(rust_id);
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();
        for item in associated_items.in_definition_order() {
            use rustc_middle::ty::AssocKind;

            let has_default_value = item.defaultness(tcx).has_value();
            // Skip the provided methods for the trait declarations, but still
            // remember their name.
            if item.kind == AssocKind::Fn && has_default_value {
                let name = bt_ctx.t_ctx.translate_trait_method_name(item.def_id);
                provided_methods.push(name);
                continue;
            }

            match &item.kind {
                AssocKind::Fn => {
                    let method_name = bt_ctx.t_ctx.translate_trait_method_name(item.def_id);
                    let fun_id = bt_ctx.translate_fun_decl_id(item.def_id);
                    required_methods.push((method_name, fun_id));
                }
                AssocKind::Const => {
                    // Check if the constant has a value (i.e., a body).
                    // We are handling a trait *declaration* so we need to
                    // check whether the constant has a default value.
                    trace!("id: {:?}\n- item: {:?}", rust_id, item);
                    let const_id =
                        // Declaration
                        if has_default_value {
                            Some(bt_ctx.translate_global_decl_id(item.def_id))
                        } else {
                            None
                        };

                    let ty = bt_ctx.translate_ety(
                        &tcx.type_of(item.def_id)
                            .subst_identity()
                            .sinto(&bt_ctx.hax_state),
                    );

                    //let const_id = bt_ctx.translate_global_decl_id(item.def_id);
                    /*                    let item_id = tcx
                        .hir()
                        .local_def_id_to_hir_id(item.def_id.as_local().unwrap());
                    let item = tcx.hir().find(item_id).unwrap();
                    trace!("Const trait item:\n{:?}", item);
                    unimplemented!("Const trait item: {:?}", item)*/
                }
                AssocKind::Type => {
                    unimplemented!("Type trait item: {:?}", item)
                }
            }
        }

        // In case of a trait implementation, some values may not have been
        // provided, in case the declaration provided default values. We
        // check those, and lookup the relevant values.

        let trait_decl = ast::TraitDecl {
            def_id,
            name,
            generics: bt_ctx.get_generics(),
            required_methods,
            provided_methods,
        };
        self.trait_decls.insert(def_id, trait_decl)
    }

    pub(crate) fn translate_trait_impl(&mut self, rust_id: DefId) {
        let def_id = self.translate_trait_impl_id(rust_id);
        let tcx = self.tcx;
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        let name = names_utils::extended_def_id_to_name(&rust_id.sinto(&bt_ctx.hax_state));

        // Translate the generics
        let _substs = bt_ctx.translate_generics(rust_id);

        // Translate the predicates
        bt_ctx.translate_predicates_of(rust_id);

        trace!("- trait id: {:?}\n- trait name: {:?}", rust_id, name);
        trace!("Trait predicates: {:?}", tcx.predicates_of(rust_id));

        // Retrieve the information about the implemented trait.
        let (impl_trait_rust_id, impl_trait) =
            if let rustc_hir::def::DefKind::Impl { .. } = tcx.def_kind(rust_id) {
                let trait_rust_id = tcx.trait_id_of_impl(rust_id).unwrap();
                let trait_id = bt_ctx.translate_trait_decl_id(trait_rust_id);
                let rustc_middle::ty::ImplSubject::Trait(trait_ref) =
                    tcx.impl_subject(rust_id).subst_identity() else { unreachable!() };
                let trait_ref = trait_ref.sinto(&bt_ctx.hax_state);
                let (regions, types, const_generics) = bt_ctx
                    .translate_substs(None, &trait_ref.generic_args)
                    .unwrap();
                let generics = GenericArgs {
                    regions,
                    types,
                    const_generics,
                    trait_refs: Vec::new(),
                };
                let trait_ref = ImplTraitRef { trait_id, generics };
                (trait_rust_id, trait_ref)
            } else {
                unreachable!()
            };

        // Explore the associated items
        // We do something subtle here: TODO
        let tcx = bt_ctx.t_ctx.tcx;
        let associated_items = tcx.associated_items(rust_id);
        let mut required_methods = Vec::new();
        let mut provided_methods = Vec::new();
        for item in associated_items.in_definition_order() {
            use rustc_middle::ty::AssocKind;

            let has_default_value = item.defaultness(tcx).has_value();
            match &item.kind {
                AssocKind::Fn => {
                    let method_name = bt_ctx.t_ctx.translate_trait_method_name(item.def_id);
                    let fun_id = bt_ctx.translate_fun_decl_id(item.def_id);

                    // Check if we implement a required method or reimplement
                    // a provided method
                    if has_default_value {
                        provided_methods.push((method_name, fun_id));
                    } else {
                        required_methods.push((method_name, fun_id));
                    }
                }
                AssocKind::Const => {
                    // Check if the constant has a value (i.e., a body).
                    // This is a trait *implementation*: the constant *must*
                    // have an implementation.
                    trace!("id: {:?}\n- item: {:?}", rust_id, item);
                    let const_id = bt_ctx.translate_global_decl_id(item.def_id);
                    let ty = bt_ctx.translate_ety(
                        &tcx.type_of(item.def_id)
                            .subst_identity()
                            .sinto(&bt_ctx.hax_state),
                    );

                    //let const_id = bt_ctx.translate_global_decl_id(item.def_id);
                    /*                    let item_id = tcx
                        .hir()
                        .local_def_id_to_hir_id(item.def_id.as_local().unwrap());
                    let item = tcx.hir().find(item_id).unwrap();
                    trace!("Const trait item:\n{:?}", item);
                    unimplemented!("Const trait item: {:?}", item)*/
                }
                AssocKind::Type => {
                    unimplemented!("Type trait item: {:?}", item)
                }
            }
        }

        // In case of a trait implementation, some values may not have been
        // provided, in case the declaration provided default values. We
        // check those, and lookup the relevant values.

        let trait_impl = ast::TraitImpl {
            def_id,
            name,
            impl_trait,
            generics: bt_ctx.get_generics(),
            required_methods,
            provided_methods,
        };
        self.trait_impls.insert(def_id, trait_impl)
    }
}
