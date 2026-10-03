//! The MIR uses a unique `return` node, which can be an issue when reconstructing
//! the control-flow.
//!
//! For instance, it often leads to code of the following shape:
//! ```text
//! if b {
//!   ...
//!   x = 0;
//! }
//! else {
//!   ...
//!   x = 1;
//! }
//! return x;
//! ```
//!
//! while a more natural reconstruction would be:
//! ```text
//! if b {
//!   ...
//!   return 0;
//! }
//! else {
//!   ...
//!   return 1;
//! }
//! ```
//!
//! Similarly, give each unwind edge its own cleanup path.

use crate::ids::Generator;
use crate::transform::TransformCtx;
use crate::ullbc_ast::*;
use crate::utils::ensure_sufficient_stack;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use crate::transform::ctx::UllbcPass;

pub struct Transform;
fn is_return_block(block: &BlockData) -> bool {
    block.terminator.kind.is_return()
        && block
            .statements
            .iter()
            .all(|st| matches!(st.kind, StatementKind::StorageDead(_)))
}

/// Duplicate the sub-control-flow-graph reachable from `id`, and return the start of the new path.
/// Unwind paths may contain loops, we're careful not to break them.
fn duplicate_unwind_path(
    blocks: &mut BodyContents,
    id: BlockId,
    // Stack of blocks we've already copied along the current path.
    copied_ancestors: &mut HashMap<BlockId, BlockId>,
) -> BlockId {
    ensure_sufficient_stack(|| {
        if let Some(&copy_id) = copied_ancestors.get(&id) {
            return copy_id;
        }
        let mut block = blocks[id].clone();
        let new_id = blocks.push(BlockData::new_unreachable(true));
        copied_ancestors.insert(id, new_id);
        for target in block.terminator.targets_mut() {
            *target = duplicate_unwind_path(blocks, *target, copied_ancestors);
        }
        copied_ancestors.remove(&id);
        blocks[new_id] = block;
        new_id
    })
}

impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, b: &mut ExprBody) {
        // Find the return block id (there should be one).
        let returns: HashMap<BlockId, BlockData> = b
            .body
            .iter_enumerated()
            .filter_map(|(bid, block)| {
                if is_return_block(block) {
                    Some((bid, block.clone()))
                } else {
                    None
                }
            })
            .collect();

        // Whenever we find a goto the return block, introduce an auxiliary block
        // for this (remark: in the end, it makes the return block dangling).
        // We do this in two steps.
        // First, introduce fresh ids.
        let mut generator = Generator::new_with_init_value(b.body.next_idx());
        let mut new_blocks = Vec::new();
        b.visit_block_ids_mut(|bid: &mut BlockId| {
            if let Some(block) = returns.get(bid) {
                *bid = generator.fresh_id();
                new_blocks.push(block.clone());
            }
        });

        // Then introduce the new blocks
        for block in new_blocks {
            let _ = b.body.push(block);
        }

        // Walk through the control-flow until we find the start of an unwind path, then copy it.
        let mut pending: Vec<BlockId> = vec![START_BLOCK_ID];
        let mut visited: HashSet<BlockId> = HashSet::default();
        let mut ancestors: HashMap<BlockId, BlockId> = HashMap::default();
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            pending.extend(b.body[id].targets_ignoring_unwind());
            let mut terminator = b.body[id].terminator.clone();
            let on_unwind = match &mut terminator.kind {
                TerminatorKind::Call { on_unwind, .. }
                | TerminatorKind::Drop { on_unwind, .. }
                | TerminatorKind::Assert { on_unwind, .. }
                | TerminatorKind::InlineAsm { on_unwind, .. } => on_unwind,
                _ => continue,
            };
            *on_unwind = duplicate_unwind_path(&mut b.body, *on_unwind, &mut ancestors);
            b.body[id].terminator = terminator;
        }
    }
}
