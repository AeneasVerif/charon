//! Replace variables bound at the top-level with `Free` vars. This is for convenience for
//! consumers of the charon ast.
use derive_generic_visitor::*;
use index_vec::Idx;

use crate::ast::*;

use super::{ctx::TransformPass, TransformCtx};

/// Replace variables bound at the top-level with `Free` vars.
#[derive(Default, Visitor)]
pub(crate) struct UnbindVarVisitor {
    // Tracks the depth of binders we're inside of.
    binder_depth: DeBruijnId,
}

impl VisitAstMut for UnbindVarVisitor {
    fn enter_region_binder<T: AstVisitable>(&mut self, _: &mut RegionBinder<T>) {
        self.binder_depth = self.binder_depth.incr()
    }
    fn exit_region_binder<T: AstVisitable>(&mut self, _: &mut RegionBinder<T>) {
        self.binder_depth = self.binder_depth.decr()
    }
    fn enter_binder<T: AstVisitable>(&mut self, _: &mut Binder<T>) {
        self.binder_depth = self.binder_depth.incr()
    }
    fn exit_binder<T: AstVisitable>(&mut self, _: &mut Binder<T>) {
        self.binder_depth = self.binder_depth.decr()
    }

    fn exit_de_bruijn_var<T: AstVisitable + Idx>(&mut self, var: &mut DeBruijnVar<T>) {
        match var {
            DeBruijnVar::Bound(dbid, varid) if *dbid == self.binder_depth => {
                *var = DeBruijnVar::Free(*varid)
            }
            DeBruijnVar::Bound(..) => {}
            DeBruijnVar::Free(_) => unreachable!("Found unexpected free variable"),
        }
    }
}

pub struct Check;
impl TransformPass for Check {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let mut visitor = UnbindVarVisitor::default();
        for mut item in ctx.translated.all_items_mut() {
            let _ = item.drive_mut(&mut visitor);
        }
    }
}
