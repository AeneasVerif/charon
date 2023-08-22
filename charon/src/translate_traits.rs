#![allow(dead_code)]
use crate::gast::TraitMethodName;
use crate::names_utils;
use crate::translate_ctx::*;
use crate::ullbc_ast as ast;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    pub(crate) fn translate_trait_method_name(&mut self, rust_id: DefId) -> TraitMethodName {
        // Just making sure we register the def id
        let _ = self.translate_fun_decl_id(rust_id);

        // Translate the name
        let name = names_utils::item_def_id_to_name(self.tcx, rust_id);
        TraitMethodName(name.name.last().unwrap().as_ident().clone())
    }

    pub(crate) fn translate_trait(&mut self, rust_id: DefId) {
        // TODO: finish
        let def_id = self.translate_trait_id(rust_id);
        let name = names_utils::extended_def_id_to_name(&rust_id.sinto(&self.hax_state));

        // Translate the generics
        let (mut bt_ctx, _substs) = self.translate_generics(rust_id);

        // Translate the predicates
        bt_ctx.translate_predicates_of(rust_id);

        trace!("- trait id: {:?}\n- trait name: {:?}", rust_id, name);

        let trait_decl = ast::TraitDecl {
            def_id,
            name,
            region_params: bt_ctx.region_vars.clone(),
            type_params: bt_ctx.type_vars.clone(),
            const_generic_params: bt_ctx.const_generic_vars.clone(),
            trait_clauses: bt_ctx.trait_clauses.clone(),
        };

        self.trait_defs.insert(def_id, trait_decl)
    }
}
