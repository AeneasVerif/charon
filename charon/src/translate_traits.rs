#![allow(dead_code)]
use crate::names_utils::extended_def_id_to_name;
use crate::translate_ctx::*;
use crate::ullbc_ast as ast;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    pub(crate) fn translate_trait(&mut self, rust_id: DefId) {
        // TODO: finish
        let def_id = self.translate_trait_id(rust_id);
        let name = extended_def_id_to_name(&rust_id.sinto(&self.hax_state));

        self.trait_defs
            .insert(def_id, ast::TraitDecl { def_id, name })
    }
}
