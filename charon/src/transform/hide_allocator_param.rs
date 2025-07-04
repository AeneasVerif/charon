use derive_generic_visitor::*;
use itertools::Itertools;
use std::collections::HashSet;

use crate::{ast::*, name_matcher::NamePattern};

use super::{ctx::TransformPass, TransformCtx};

#[derive(Visitor)]
struct RemoveLastParamVisitor {
    types: HashSet<TypeDeclId>,
}

impl VisitAstMut for RemoveLastParamVisitor {
    fn enter_type_decl_ref(&mut self, x: &mut TypeDeclRef) {
        if x.id.as_adt().is_some_and(|id| self.types.contains(id))
            || x.id.as_builtin().is_some_and(|b| b.is_box())
        {
            // Remove the last param.
            x.generics.types.pop();
        }
    }
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        if !ctx.options.hide_allocator {
            return;
        }
        // TODO: add Vec, Rc, etc
        let types = &["alloc::boxed::Box"];

        let types: Vec<NamePattern> = types
            .into_iter()
            .map(|s| NamePattern::parse(s).unwrap())
            .collect_vec();
        let types: HashSet<TypeDeclId> = ctx
            .translated
            .item_names
            .iter()
            .filter(|(_, name)| types.iter().any(|p| p.matches(&ctx.translated, name)))
            .filter_map(|(id, _)| id.as_type())
            .copied()
            .collect();

        for &id in &types {
            if let Some(tdecl) = ctx.translated.type_decls.get_mut(id) {
                tdecl.generics.types.pop();
            }
        }

        let _ = ctx
            .translated
            .drive_mut(&mut RemoveLastParamVisitor { types });
    }
}
