//! Remove unused trait clauses from items. A clause is unused if it is only used to build proofs
//! for other unused clauses.
use derive_generic_visitor::*;
use petgraph::visit::Walker;
use petgraph::{graphmap::DiGraphMap, visit::Dfs};
use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::ids::IndexVec;

use crate::transform::{TransformCtx, ctx::TransformPass};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ClauseNode {
    /// A special node to indicate clauses that we consider unconditionally used. Unused clauses
    /// will in the end be the ones unreachable from the root.
    Root,
    /// The nth clause parameter of that item.
    Clause(ItemId, TraitClauseId),
}

#[derive(Visitor)]
struct BuildGraphVisitor<'a> {
    graph: &'a mut DiGraphMap<ClauseNode, ()>,
    /// The item we're visiting.
    current_item: ItemId,
    /// The node currently using the part of the AST we're visiting.
    current_context: ClauseNode,
    binder_depth: DeBruijnId,
}

impl VisitorWithBinderDepth for BuildGraphVisitor<'_> {
    fn binder_depth_mut(&mut self) -> &mut DeBruijnId {
        &mut self.binder_depth
    }
}

impl VisitorWithItemRef for BuildGraphVisitor<'_> {
    fn visit_item_ref(
        &mut self,
        item_id: ItemId,
        args: &GenericArgs,
    ) -> ControlFlow<<Self as Visitor>::Break> {
        let GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        } = args;
        self.visit(regions)?;
        self.visit(types)?;
        self.visit(const_generics)?;
        let old_context = self.current_context;
        for (clause_id, trait_ref) in trait_refs.iter_enumerated() {
            self.current_context = ClauseNode::Clause(item_id, clause_id);
            self.visit(trait_ref)?;
        }
        self.current_context = old_context;
        Continue(())
    }
}

impl VisitAst for BuildGraphVisitor<'_> {
    fn visit<T: AstVisitable>(&mut self, x: &T) -> ControlFlow<Self::Break> {
        VisitWithBinderDepth::new(VisitWithItemRef::new(self)).visit(x)
    }

    fn visit_trait_param(&mut self, x: &TraitParam) -> ControlFlow<Self::Break> {
        // Check if this is a clause definition at the level of the item. If so, we want to track
        // inter-clause dependencies such as `TraitClause1: (TraitClause0::Item: Copy)`.
        if self.binder_depth == DeBruijnId::ZERO && x.origin != PredicateOrigin::WhereClauseOnTrait
        {
            let old_context = self.current_context;
            self.current_context = ClauseNode::Clause(self.current_item, x.clause_id);
            self.visit(&x.trait_)?;
            self.current_context = old_context;
            Continue(())
        } else {
            self.visit_inner(x)
        }
    }

    fn enter_trait_ref_kind(&mut self, x: &TraitRefKind) {
        if let TraitRefKind::Clause(var) = x
            && let Some(clause_id) = var.bound_at_depth(self.binder_depth)
        {
            self.graph.add_edge(
                self.current_context,
                ClauseNode::Clause(self.current_item, clause_id),
                (),
            );
        }
    }
}

#[derive(Visitor)]
struct RemoveClausesVisitor<'a> {
    /// For each item, a map from old clause ids to new ones. The new ones are in the same order,
    /// just skipping some removed old ones.
    remaps: &'a HashMap<ItemId, IndexVec<TraitClauseId, Option<TraitClauseId>>>,
    current_item: ItemId,
    binder_depth: DeBruijnId,
}

impl VisitorWithBinderDepth for RemoveClausesVisitor<'_> {
    fn binder_depth_mut(&mut self) -> &mut DeBruijnId {
        &mut self.binder_depth
    }
}

impl VisitorWithItemRefMut for RemoveClausesVisitor<'_> {
    fn enter_item_ref(&mut self, item_id: ItemId, args: &mut GenericArgs) {
        if let Some(remap) = self.remaps.get(&item_id) {
            for (old_id, trait_ref) in std::mem::take(&mut args.trait_refs).into_iter_enumerated() {
                if remap[old_id].is_some() {
                    args.trait_refs.push(trait_ref);
                }
            }
        }
    }
}

impl VisitAstMut for RemoveClausesVisitor<'_> {
    fn visit<T: AstVisitable>(&mut self, x: &mut T) -> ControlFlow<Self::Break> {
        VisitWithBinderDepth::new(VisitWithItemRef::new(self)).visit(x)
    }

    fn visit_trait_ref_kind(&mut self, x: &mut TraitRefKind) -> ControlFlow<Self::Break> {
        if let TraitRefKind::Clause(var) = x
            && let Some(clause_id) = var.bound_at_depth_mut(self.binder_depth)
            && let Some(remap) = self.remaps.get(&self.current_item)
        {
            *clause_id = remap[*clause_id].expect("mismatch while trying to remove unused clauses");
        }
        self.visit_inner(x)
    }
}

pub struct Transform;
impl TransformPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.remove_unused_clauses || options.remove_unused_self_clauses
    }

    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // Build a dependency graph between all item clauses of the crate.
        let graph: DiGraphMap<ClauseNode, ()> = {
            let mut graph = DiGraphMap::new();
            for item in ctx.translated.all_items() {
                let item_id = item.id();
                let is_opaque_fn = item.as_fun().is_some_and(|decl| !decl.body.has_contents());

                for clause in &item.generic_params().trait_clauses {
                    // For opaque bodies, we must assume they may be using any clause in scope.
                    let may_remove_clause = !is_opaque_fn
                        && (ctx.options.remove_unused_clauses
                            || (ctx.options.remove_unused_self_clauses
                                && clause.origin == PredicateOrigin::TraitSelf));
                    if !may_remove_clause {
                        let clause_id = clause.clause_id;
                        graph.add_edge(
                            ClauseNode::Root,
                            ClauseNode::Clause(item_id, clause_id),
                            (),
                        );
                    }
                }

                let mut visitor = BuildGraphVisitor {
                    graph: &mut graph,
                    current_item: item_id,
                    binder_depth: DeBruijnId::ZERO,
                    current_context: ClauseNode::Root,
                };
                item.drive(&mut visitor);
            }
            graph
        };

        // Remove the unused clauses and collect a global remapping of clause ids.
        let remaps: HashMap<ItemId, IndexVec<TraitClauseId, Option<TraitClauseId>>> = {
            let reachable: HashSet<ClauseNode> =
                Dfs::new(&graph, ClauseNode::Root).iter(&graph).collect();
            ctx.translated
                .all_items_mut()
                .filter_map(|mut item| {
                    let item_id = item.as_ref().id();
                    let item_clauses = &mut item.generic_params().trait_clauses;
                    let clauses_to_remove: HashSet<TraitClauseId> = item_clauses
                        .indices()
                        .filter(|clause_id| {
                            !reachable.contains(&ClauseNode::Clause(item_id, *clause_id))
                        })
                        .collect();
                    if clauses_to_remove.is_empty() {
                        return None;
                    }
                    let remap: IndexVec<TraitClauseId, Option<TraitClauseId>> =
                        std::mem::take(item_clauses).map_indexed(|old_id, mut clause| {
                            if clauses_to_remove.contains(&old_id) {
                                None
                            } else {
                                let new_id = item_clauses.push_with(|new_id| {
                                    clause.clause_id = new_id;
                                    clause
                                });
                                Some(new_id)
                            }
                        });
                    Some((item_id, remap))
                })
                .collect()
        };

        // Adjust references to clauses.
        for mut item in ctx.translated.all_items_mut() {
            let item_id = item.as_ref().id();
            item.drive_mut(&mut RemoveClausesVisitor {
                remaps: &remaps,
                current_item: item_id,
                binder_depth: DeBruijnId::ZERO,
            });
        }
    }
}
