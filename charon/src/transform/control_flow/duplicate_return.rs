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

use crate::ids::Generator;
use crate::transform::TransformCtx;
use crate::ullbc_ast::*;
use std::collections::HashMap;

use crate::transform::ctx::UllbcPass;

pub struct Transform;
fn is_return_block(block: &BlockData) -> bool {
    block.terminator.kind.is_return()
        && block
            .statements
            .iter()
            .all(|st| matches!(st.kind, StatementKind::StorageDead(_)))
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
        b.body.dyn_visit_in_body_mut(|bid: &mut BlockId| {
            if let Some(block) = returns.get(bid) {
                *bid = generator.fresh_id();
                new_blocks.push(block.clone());
            }
        });

        // Then introduce the new blocks
        for block in new_blocks {
            let _ = b.body.push(block);
        }
    }
}
