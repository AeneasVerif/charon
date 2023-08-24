#![allow(dead_code)]
use crate::gast::TraitMethodName;
use crate::names_utils;
use crate::translate_ctx::*;
use crate::ullbc_ast as ast;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;
use std::collections::HashSet;

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    pub(crate) fn translate_trait_method_name(&mut self, rust_id: DefId) -> TraitMethodName {
        // Just making sure we register the def id
        let _ = self.translate_fun_decl_id(rust_id);

        // Translate the name
        let name = names_utils::item_def_id_to_name(self.tcx, rust_id);
        TraitMethodName(name.name.last().unwrap().as_ident().clone())
    }

    pub(crate) fn translate_trait(&mut self, rust_id: DefId) {
        let def_id = self.translate_trait_decl_id(rust_id);

        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        let name = names_utils::extended_def_id_to_name(&rust_id.sinto(&bt_ctx.hax_state));

        // Translate the generics
        let _substs = bt_ctx.translate_generics(rust_id);

        // Translate the predicates
        bt_ctx.translate_predicates_of(rust_id);

        trace!("- trait id: {:?}\n- trait name: {:?}", rust_id, name);

        // Explore the associated items
        let tcx = bt_ctx.t_ctx.tcx;

        // Retrieve the provided methods. The provided methods
        // are the methods with a default implementation.
        // We do this to filter the provided methods from the associated
        // items - see the documentation of [TraitDecl] for the full details.
        let provided_methods: HashSet<DefId> = tcx
            .provided_trait_methods(rust_id)
            .map(|assoc| assoc.def_id)
            .collect();

        // Retrieve the associated items
        let associated_items = tcx.associated_items(rust_id);

        let mut functions = Vec::new();
        for item in associated_items.in_definition_order() {
            use rustc_middle::ty::AssocKind;
            // Filter the provided methods
            if provided_methods.contains(&item.def_id) {
                continue;
            }

            match &item.kind {
                AssocKind::Fn => {
                    let method_name = bt_ctx.t_ctx.translate_trait_method_name(item.def_id);
                    let fun_id = bt_ctx.translate_fun_decl_id(item.def_id);
                    functions.push((method_name, fun_id));
                }
                AssocKind::Const => {
                    unimplemented!("Const trait item: {:?}", item)
                }
                AssocKind::Type => {
                    unimplemented!("Type trait item: {:?}", item)
                }
            }
        }

        let trait_decl = ast::TraitDecl {
            def_id,
            name,
            generics: bt_ctx.get_generics(),
            functions,
        };
        self.trait_defs.insert(def_id, trait_decl)
    }
}
