//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

use crate::hax;

use super::translate_ctx::*;
use charon_lib::ast::*;

impl<'tcx> ItemTransCtx<'tcx, '_> {
    /// Translate the names of the arguments of this definition, if they are available,
    /// otherwise naming arguments `arg0`, `arg1`, etc.
    /// Note that the names of the arguments are not always available, even when
    /// we can retrieve the MIR body, in which case we also fall back to `argN`.
    pub fn translate_argument_names(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
        n_args: usize,
    ) -> Vec<Option<String>> {
        let Ok(Some(body)) = self.get_mir(def.this(), span) else {
            return vec![None; n_args];
        };
        body.local_decls
            .iter_enumerated()
            .skip(1)
            .take(body.arg_count)
            .map(|(index, _)| hax::name_of_local(index, &body.var_debug_info))
            .collect()
    }
}
