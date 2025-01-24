//! In the MIR AST, it seems `assert` are introduced to check preconditions
//! (for the binops for example). The `assert!` introduced by the user
//! introduce `if ... then { panic!(...) } else { ...}`.
//! This pass introduces `assert` instead in order to make the code shorter.

use std::collections::HashSet;

use crate::transform::TransformCtx;
use crate::ullbc_ast::*;

use super::ctx::UllbcPass;

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, b: &mut ExprBody) {
        // Start by computing the set of blocks which are actually panics.
        // Remark: doing this in two steps because reading the blocks at random
        // while doing in-place updates is not natural to do in Rust.
        let panics: HashSet<BlockId> = b
            .body
            .iter_indexed()
            .filter_map(|(bid, block)| {
                if block.statements.is_empty() && block.terminator.content.is_abort() {
                    Some(bid)
                } else {
                    None
                }
            })
            .collect();

        for block in b.body.iter_mut() {
            match &block.terminator.content {
                RawTerminator::Switch {
                    discr: _,
                    targets: SwitchTargets::If(bid0, bid1),
                } => {
                    let (nbid, expected) = if panics.contains(bid0) {
                        (*bid1, false)
                    } else if panics.contains(bid1) {
                        (*bid0, true)
                    } else {
                        continue;
                    };

                    let content = std::mem::replace(
                        &mut block.terminator.content,
                        RawTerminator::Goto { target: nbid },
                    );
                    let (discr, _) = content.as_switch().unwrap();
                    block.statements.push(Statement::new(
                        block.terminator.span,
                        RawStatement::Assert(Assert {
                            cond: discr.clone(),
                            expected,
                        }),
                    ));
                }
                _ => (),
            }
        }
    }
}
