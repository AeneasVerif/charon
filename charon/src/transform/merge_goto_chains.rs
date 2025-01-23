//! # Micro-pass: merge single-origin gotos into their parent to reduce CFG graph size.
use crate::ids::Vector;
use crate::transform::TransformCtx;
use crate::ullbc_ast::*;

use super::ctx::UllbcPass;

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, ctx: &mut TransformCtx, body: &mut ExprBody) {
        // Check the option which instructs to ignore this pass
        if ctx.options.no_merge_goto_chains {
            return;
        }

        // Compute for each block the number of blocks that points to it.
        let mut antecedents: Vector<BlockId, usize> = body.body.map_ref(|_| 0);
        for block in body.body.iter() {
            for target in block.targets() {
                *antecedents.get_mut(target).unwrap() += 1;
            }
        }
        // Merge blocks with a single antecedent into their antecedent.
        for id in body.body.all_indices() {
            while let Some(source) = body.body.get(id)
                && let RawTerminator::Goto { target } = source.terminator.content
                && antecedents[target] == 1
            {
                let mut target = body.body.remove(target).unwrap();
                let source = &mut body.body[id];
                source.statements.append(&mut target.statements);
                source.terminator = target.terminator;
            }
        }
    }
}
