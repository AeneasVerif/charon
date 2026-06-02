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
    binder_stack: BindingStack<GenericParams>,
}

impl<'a> ClauseExtractor<'a> {
    fn new(params: &'a mut GenericParams, span: Span) -> Self {
        Self {
            binder_stack: BindingStack::new(params.clone()),
            params,
            span,
        }
    }

    /// Move a trait ref out of the binders to make it a trait clause. Collects all the region
    /// binders on the way to here into a single binder to make a HRTB.
    fn extract_trait_clause(&self, mut trait_: PolyTraitDeclRef) -> Option<PolyTraitDeclRef> {
        // Iterate over the binders on the way to this trait ref, skipping the first binder (the
        // item binder).
        let mut scope_regions = Vec::new();
        for (dbid, params) in self.binder_stack.iter_enumerated().rev().skip(1) {
            for (old_id, region) in params.regions.iter_enumerated() {
                let new_id = trait_.regions.push_with(|index| {
                    let mut region = region.clone();
                    region.index = index;
                    region
                });
                scope_regions.push((dbid, old_id, new_id));
            }
        }

        if !scope_regions.is_empty() {
            // Make all the region variables point at the outer binder.
            #[derive(Visitor)]
            struct MoveRegionsToHrtb {
                binder_depth: DeBruijnId,
                scope_regions: Vec<(DeBruijnId, RegionId, RegionId)>,
            }

            impl VisitorWithBinderDepth for MoveRegionsToHrtb {
                fn binder_depth_mut(&mut self) -> &mut DeBruijnId {
                    &mut self.binder_depth
                }
            }

            impl VisitAstMut for MoveRegionsToHrtb {
                fn visit<T: AstVisitable>(&mut self, x: &mut T) -> ControlFlow<Self::Break> {
                    VisitWithBinderDepth::new(self).visit(x)
                }

                fn enter_region(&mut self, region: &mut Region) {
                    let Region::Var(var) = region else {
                        return;
                    };
                    let DeBruijnVar::Bound(dbid, old_id) = *var else {
                        return;
                    };
                    let Some(outer_depth) = dbid.sub(self.binder_depth.incr()) else {
                        return;
                    };
                    let Some((_, _, new_id)) = self
                        .scope_regions
                        .iter()
                        .find(|(dbid, id, _)| *dbid == outer_depth && *id == old_id)
                    else {
                        return;
                    };
                    *var = DeBruijnVar::bound(self.binder_depth, *new_id);
                }
            }

            MoveRegionsToHrtb {
                binder_depth: DeBruijnId::zero(),
                scope_regions,
            }
            .visit(&mut trait_.skip_binder);
        }

        trait_.move_from_under_binders(self.binder_stack.depth())
    }
}

impl VisitorWithBinderStack for ClauseExtractor<'_> {
    fn binder_stack_mut(&mut self) -> &mut BindingStack<GenericParams> {
        &mut self.binder_stack
    }
}

impl VisitAstMut for ClauseExtractor<'_> {
    fn visit<T: AstVisitable>(&mut self, x: &mut T) -> ControlFlow<Self::Break> {
        VisitWithBinderStack::new(self).visit(x)
    }

    fn exit_trait_ref_contents(&mut self, tref: &mut TraitRefContents) {
        if matches!(tref.kind, TraitRefKind::Unknown(_))
            && let Some(trait_) = self.extract_trait_clause(tref.trait_decl_ref.clone())
        {
            let clause_id = self.params.trait_clauses.push_with(|clause_id| TraitParam {
                clause_id,
                span: Some(self.span),
                origin: PredicateOrigin::WhereClauseOnType,
                trait_,
            });
            tref.kind =
                TraitRefKind::Clause(DeBruijnVar::bound(self.binder_stack.depth(), clause_id));
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
