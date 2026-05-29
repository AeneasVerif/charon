//! Rust doesn't require bounds on type aliases to be well-formed. When a type alias mentions
//! `<T as Trait>::Assoc` without a corresponding `T: Trait` clause, translation leaves an unknown
//! trait ref. This pass tries to add these missing clauses.
use derive_generic_visitor::*;

use crate::ast::*;
use crate::transform::{TransformCtx, ctx::TransformPass};

#[derive(Visitor)]
struct ClauseExtractor<'a> {
    params: &'a mut GenericParams,
    span: Span,
    binder_depth: DeBruijnId,
}

impl<'a> ClauseExtractor<'a> {
    fn new(params: &'a mut GenericParams, span: Span) -> Self {
        Self {
            binder_depth: DeBruijnId::zero(),
            params,
            span,
        }
    }
}

impl VisitorWithBinderDepth for ClauseExtractor<'_> {
    fn binder_depth_mut(&mut self) -> &mut DeBruijnId {
        &mut self.binder_depth
    }
}

impl VisitAstMut for ClauseExtractor<'_> {
    fn visit<T: AstVisitable>(&mut self, x: &mut T) -> ControlFlow<Self::Break> {
        VisitWithBinderDepth::new(self).visit(x)
    }

    fn exit_trait_ref_contents(&mut self, tref: &mut TraitRefContents) {
        if matches!(tref.kind, TraitRefKind::Unknown(_))
            && let Some(trait_) = tref
                .trait_decl_ref
                .clone()
                .move_from_under_binders(self.binder_depth)
        {
            let clause_id = self.params.trait_clauses.push_with(|clause_id| TraitParam {
                clause_id,
                span: Some(self.span),
                origin: PredicateOrigin::WhereClauseOnType,
                trait_,
            });
            tref.kind = TraitRefKind::Clause(DeBruijnVar::bound(self.binder_depth, clause_id));
        }
    }
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        for tdecl in &mut ctx.translated.type_decls {
            if let TypeDeclKind::Alias(ty) = &mut tdecl.kind {
                ClauseExtractor::new(&mut tdecl.generics, tdecl.item_meta.span).visit(ty);
            }
        }
    }
}
