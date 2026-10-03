//! Renumber rechable blocks to be consecutive and in topological order (ignoring loop backedges).
use std::mem;

use itertools::Itertools;
use petgraph::graphmap::DiGraphMap;
use petgraph::visit::{DfsPostOrder, Walker};

use crate::ids::*;
use crate::transform::TransformCtx;
use crate::ullbc_ast::*;

use crate::transform::ctx::UllbcPass;

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, b: &mut ExprBody) {
        let mut graph = DiGraphMap::<BlockId, ()>::new();
        for (id, block) in b.body.iter_enumerated() {
            for target in block.targets() {
                graph.add_edge(id, target, ());
            }
        }

        let mut old_blocks = mem::take(&mut b.body);
        let mut id_map: IndexVec<BlockId, Option<BlockId>> = old_blocks.map_ref(|_| None);
        let postorder = DfsPostOrder::new(&graph, START_BLOCK_ID)
            .iter(&graph)
            .collect_vec();
        for id in postorder.into_iter().rev() {
            let new_id = b.body.push(old_blocks[id].take());
            id_map[id] = Some(new_id);
        }

        // Update the ids.
        b.visit_block_ids_mut(|id: &mut BlockId| *id = id_map[*id].unwrap());
    }
}
