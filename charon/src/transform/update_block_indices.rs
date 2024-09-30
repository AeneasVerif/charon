//! Update the block indices to make sure they are consecutive

use crate::ids::*;
use crate::transform::TransformCtx;
use crate::ullbc_ast::*;

use super::ctx::UllbcPass;

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        // Compute the map from old ids to new ids
        let mut id_map: MapGenerator<BlockId, BlockId> = MapGenerator::new();
        for (id, _) in b.body.iter_indexed() {
            let _ = id_map.insert(id);
        }

        // Update the ids
        take_mut::take(&mut b.body, |mut body| {
            // Update the ids
            body.iter_mut().for_each(|block| {
                use RawTerminator::*;
                match &mut block.terminator.content {
                    Goto { target } => *target = id_map.get(target).unwrap(),
                    Switch { targets, .. } => {
                        use SwitchTargets::*;
                        match targets {
                            If(id0, id1) => {
                                *id0 = id_map.get(id0).unwrap();
                                *id1 = id_map.get(id1).unwrap();
                            }
                            SwitchInt(_, targets, otherwise) => {
                                for (_, id) in targets {
                                    *id = id_map.get(id).unwrap();
                                }
                                *otherwise = id_map.get(otherwise).unwrap();
                            }
                        }
                    }
                    Abort(_) | Return => (),
                }
            });
            // Reconstruct the vector to make sure there are no holes
            body.into_iter().collect()
        });
    }
}
