//! ULLBC to LLBC
//!
//! Reconstruct the control-flow of the ULLBC function bodies, using the algorithm from "Beyond
//! Relooper" (https://dl.acm.org/doi/10.1145/3547621).
use indexmap::IndexMap;
use itertools::Itertools;
use petgraph::algo::dominators::{Dominators, simple_fast};
use petgraph::graphmap::DiGraphMap;
use petgraph::visit::{DfsPostOrder, Walker};
use std::collections::HashSet;
use std::u32;

use crate::common::ensure_sufficient_stack;
use crate::formatter::IntoFormatter;
use crate::llbc_ast as tgt;
use crate::meta::{Span, combine_span};
use crate::pretty::FmtWithCtx;
use crate::transform::TransformCtx;
use crate::transform::ctx::TransformPass;
use crate::ullbc_ast::{self as src, BlockId};
use crate::{ast::*, register_error};

fn translate_statement(st: &src::Statement) -> tgt::Statement {
    let kind = match st.kind.clone() {
        src::StatementKind::Assign(place, rvalue) => tgt::StatementKind::Assign(place, rvalue),
        src::StatementKind::SetDiscriminant(place, variant_id) => {
            tgt::StatementKind::SetDiscriminant(place, variant_id)
        }
        src::StatementKind::CopyNonOverlapping(copy) => {
            tgt::StatementKind::CopyNonOverlapping(copy)
        }
        src::StatementKind::StorageLive(var_id) => tgt::StatementKind::StorageLive(var_id),
        src::StatementKind::StorageDead(var_id) => tgt::StatementKind::StorageDead(var_id),
        src::StatementKind::Deinit(place) => tgt::StatementKind::Deinit(place),
        src::StatementKind::Assert(assert) => tgt::StatementKind::Assert(assert),
        src::StatementKind::Nop => tgt::StatementKind::Nop,
        src::StatementKind::Error(s) => tgt::StatementKind::Error(s),
    };
    tgt::Statement::new(st.span, kind)
}

enum SpecialJump {
    Loop,
    Block,
}

struct ReloopCtx<'a> {
    /// List of source blocks to translate.
    blocks: &'a Vector<BlockId, src::BlockData>,
    /// Locals for the target body, so that we can add intermediate variables.
    locals: Locals,
    /// Reverse postorder numbering of the blocks. Using `u32` is fine because we already limit
    /// `BlockId`s to `u32::MAX`.
    reverse_postorder: Vector<BlockId, u32>,
    /// Dominator tree.
    dominator_tree: Dominators<BlockId>,
    /// The (unique) entrypoints of each loop. Unique because we error on irreducible cfgs.
    loop_headers: HashSet<src::BlockId>,
    /// Blocks that have multiple incoming control-flow edges.
    merge_targets: HashSet<src::BlockId>,
    /// Stack of blocks we must translate specially in the current context.
    special_jump_stack: Vec<(BlockId, SpecialJump)>,
}

/// Error indicating that the control-flow graph is not reducible. The contained block id is a
/// block involved in an irreducible subgraph.
struct Irreducible(BlockId);

/// Control-Flow Graph
type Cfg = DiGraphMap<src::BlockId, ()>;

impl<'a> ReloopCtx<'a> {
    fn new(src_body: &'a src::ExprBody, start_block: BlockId) -> Result<Self, Irreducible> {
        // Explore the function body to create the control-flow graph without backward
        // edges, and identify the loop entries (which are destinations of backward edges).
        // Build the node graph (we ignore unwind paths for now).
        let mut cfg = Cfg::new();
        for (block_id, block) in src_body.body.iter_indexed() {
            cfg.add_node(block_id);
            for tgt in block.targets_ignoring_unwind() {
                cfg.add_edge(block_id, tgt, ());
            }
        }

        // Compute the dominator tree.
        let dominator_tree = simple_fast(&cfg, start_block);

        // Compute reverse postorder numbering.
        let mut reverse_postorder = src_body.body.map_ref_opt(|_| None);
        for (i, block_id) in DfsPostOrder::new(&cfg, start_block).iter(&cfg).enumerate() {
            let rev_post_id = reverse_postorder.slot_count() - i;
            assert!(rev_post_id <= u32::MAX as usize);
            reverse_postorder.set_slot(block_id, rev_post_id as u32);
        }

        // Compute the forward graph (without backward edges).
        let mut loop_headers = HashSet::new();
        let mut merge_targets = HashSet::new();
        for src in cfg.nodes() {
            if reverse_postorder.get(src).is_none() {
                // Unreachable block
                continue;
            }
            for tgt in cfg.neighbors(src) {
                // Check if the edge is a backward edge.
                if reverse_postorder[src] >= reverse_postorder[tgt] {
                    // This is a backward edge
                    loop_headers.insert(tgt);
                    // A cfg is reducible iff the target of every back edge dominates the
                    // edge's source.
                    if !dominator_tree.dominators(src).unwrap().contains(&tgt) {
                        return Err(Irreducible(src));
                    }
                }
            }
            if cfg
                .neighbors_directed(src, petgraph::Direction::Incoming)
                .count()
                >= 2
            {
                merge_targets.insert(src);
            }
        }

        Ok(ReloopCtx {
            blocks: &src_body.body,
            locals: src_body.locals.clone(),
            reverse_postorder,
            dominator_tree,
            loop_headers,
            merge_targets,
            special_jump_stack: Vec::new(),
        })
    }

    /// Translate this block and all the blocks it dominates, recursively over the dominator tree.
    /// We follow the algorithm in the paper.
    fn reloop_block(&mut self, bid: BlockId) -> tgt::Block {
        ensure_sufficient_stack(|| self.reloop_block_inner(bid))
    }
    fn reloop_block_inner(&mut self, bid: BlockId) -> tgt::Block {
        // Some of the blocks we might jump to inside this tree can't be translated as normal
        // blocks: the loop backward edges must become `continue`s and the merge nodes may need
        // some care if we're jumping to them from distant locations.
        // For this purpose, we push to the `context_stack` the block ids that must be translated
        // spoecially. In `translate_jump` we check the stack.
        let old_context_depth = self.special_jump_stack.len();

        // Catch jumps to the loop header.
        if self.loop_headers.contains(&bid) {
            self.special_jump_stack.push((bid, SpecialJump::Loop));
        }

        // Catch jumps to a merge node. The merge nodes are translated after this node, and we can
        // jump to them using `break`. The child with highest postorder numbering is nested
        // outermost in this scheme.
        let merge_children = self
            .dominator_tree
            .immediately_dominated_by(bid)
            .filter(|child| self.merge_targets.contains(child))
            .sorted_by_key(|&child| self.reverse_postorder[child]);
        for child in merge_children.rev() {
            self.special_jump_stack.push((child, SpecialJump::Block));
        }

        // Translate this block. Any jumps to the loop header or a merge node will be replaced with
        // `continue`/`break`.
        let mut block = self.translate_block(&self.blocks[bid]);

        // Pop the contexts and translate what remains.
        while self.special_jump_stack.len() > old_context_depth {
            block = tgt::Statement::new(block.span, tgt::StatementKind::Loop(block)).into_block();
            match self.special_jump_stack.pop().unwrap() {
                (_, SpecialJump::Loop) => {}
                (followed_by, SpecialJump::Block) => {
                    // We must translate the merge nodes after the block used for forward jumps to
                    // them.
                    let followed_by = self.reloop_block(followed_by);
                    block = block.merge(followed_by);
                }
            }
        }
        block
    }

    // Translate a jump between these two blocks.
    fn translate_jump(&mut self, span: Span, to: BlockId) -> tgt::Block {
        match self
            .special_jump_stack
            .iter()
            .rev()
            .enumerate()
            .find(|(_, (b, _))| *b == to)
        {
            Some((i, (_, context))) => {
                let kind = match context {
                    SpecialJump::Loop => tgt::StatementKind::Continue(i),
                    SpecialJump::Block => tgt::StatementKind::Break(i),
                };
                tgt::Statement::new(span, kind).into_block()
            }
            None => self.reloop_block(to),
        }
    }

    fn translate_block(&mut self, block: &src::BlockData) -> tgt::Block {
        // Translate the statements inside the block
        let statements = block
            .statements
            .iter()
            .map(|st| translate_statement(st))
            .collect_vec();
        let terminator = self.translate_terminator(&block.terminator);
        // Prepend the statements to the terminator.
        if let Some(st) = tgt::Block::from_seq(statements) {
            st.merge(terminator)
        } else {
            terminator
        }
    }

    fn translate_terminator(&mut self, terminator: &src::Terminator) -> tgt::Block {
        let src_span = terminator.span;
        match &terminator.kind {
            src::TerminatorKind::Abort(kind) => {
                tgt::Statement::new(src_span, tgt::StatementKind::Abort(kind.clone())).into_block()
            }
            src::TerminatorKind::Return => {
                tgt::Statement::new(src_span, tgt::StatementKind::Return).into_block()
            }
            src::TerminatorKind::UnwindResume => {
                tgt::Statement::new(src_span, tgt::StatementKind::Abort(AbortKind::Panic(None)))
                    .into_block()
            }
            src::TerminatorKind::Call {
                call,
                target,
                on_unwind: _,
            } => {
                // TODO: Have unwinds in the LLBC
                let mut block = self.translate_jump(src_span, *target);
                let st = tgt::Statement::new(src_span, tgt::StatementKind::Call(call.clone()));
                block.statements.insert(0, st);
                block
            }
            src::TerminatorKind::Drop {
                place,
                tref,
                target,
                on_unwind: _,
            } => {
                // TODO: Have unwinds in the LLBC
                let mut block = self.translate_jump(src_span, *target);
                let st = tgt::Statement::new(
                    src_span,
                    tgt::StatementKind::Drop(place.clone(), tref.clone()),
                );
                block.statements.insert(0, st);
                block
            }
            src::TerminatorKind::Goto { target } => self.translate_jump(src_span, *target),
            src::TerminatorKind::Switch { discr, targets } => {
                let switch = match &targets {
                    src::SwitchTargets::If(then_tgt, else_tgt) => {
                        let then_block = self.translate_jump(src_span, *then_tgt);
                        let else_block = self.translate_jump(src_span, *else_tgt);
                        tgt::Switch::If(discr.clone(), then_block, else_block)
                    }
                    src::SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                        // Note that some branches can be grouped together, like
                        // here:
                        // ```
                        // match e {
                        //   E::V1 | E::V2 => ..., // Grouped
                        //   E::V3 => ...
                        // }
                        // ```
                        // We detect this by checking if a block has already been
                        // translated as one of the branches of the switch.

                        // We map each block ids to a vector of matched integer values that
                        // lead to that block.
                        let mut branches: IndexMap<src::BlockId, Vec<Literal>> = IndexMap::new();
                        for (v, tgt) in targets.iter() {
                            branches.entry(*tgt).or_default().push(v.clone());
                        }

                        let targets_blocks: Vec<(Vec<Literal>, tgt::Block)> = branches
                            .into_iter()
                            .map(|(tgt, values)| {
                                let block = self.translate_jump(src_span, tgt);
                                (values, block)
                            })
                            .collect();
                        let otherwise_block = self.translate_jump(src_span, *otherwise);

                        tgt::Switch::SwitchInt(
                            discr.clone(),
                            *int_ty,
                            targets_blocks,
                            otherwise_block,
                        )
                    }
                };

                let span = tgt::combine_switch_targets_span(&switch);
                let span = combine_span(&src_span, &span);
                let st = tgt::StatementKind::Switch(switch);
                tgt::Statement::new(span, st).into_block()
            }
        }
    }
}

fn translate_body(ctx: &mut TransformCtx, body: &mut gast::Body) {
    let Body::Unstructured(src_body) = body else {
        panic!("Called `ullbc_to_llbc` on an already restructured body")
    };
    trace!("About to translate to ullbc: {:?}", src_body.span);

    let start_block = BlockId::ZERO;
    let mut reloop_ctx = match ReloopCtx::new(src_body, start_block) {
        Ok(reloop_ctx) => reloop_ctx,
        Err(Irreducible(bid)) => {
            let span = src_body.body[bid].terminator.span;
            register_error!(
                ctx,
                span,
                "the control-flow graph of this function is not reducible"
            );
            panic!("can't reconstruct irreducible control-flow")
        }
    };
    let tgt_body = reloop_ctx.reloop_block(start_block);

    *body = Body::Structured(tgt::ExprBody {
        span: src_body.span,
        locals: reloop_ctx.locals,
        comments: src_body.comments.clone(),
        body: tgt_body,
    });
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // Translate the bodies one at a time.
        ctx.for_each_body(|ctx, body| {
            translate_body(ctx, body);
        });

        // Print the functions
        let fmt_ctx = &ctx.into_fmt();
        for fun in &ctx.translated.fun_decls {
            trace!(
                "# Signature:\n{}\n\n# Function definition:\n{}\n",
                fun.signature.with_ctx(fmt_ctx),
                fun.with_ctx(fmt_ctx),
            );
        }

        if ctx.options.print_built_llbc {
            info!("# LLBC resulting from control-flow reconstruction:\n\n{ctx}\n",);
        }
    }
}
