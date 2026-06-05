use std::{collections::HashMap, mem};

use crate::transform::CowBox;
use crate::transform::{TransformCtx, ctx::UllbcPass};
use crate::ullbc_ast::*;

pub struct Transform {
    anon_consts: HashMap<GlobalDeclId, FunDeclId>,
}

impl Transform {
    pub fn new(ctx: &mut TransformCtx) -> CowBox<dyn UllbcPass> {
        // Map each anon const id to its initializer.
        let anon_consts = ctx
            .translated
            .global_decls
            .iter()
            .filter(|gdecl| matches!(gdecl.global_kind, GlobalKind::AnonConst))
            .filter_map(|gdecl| Some((gdecl.def_id, gdecl.init_fun_id()?)))
            .collect();
        CowBox::Owned(Box::new(Transform { anon_consts }))
    }
}
impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        !options.raw_consts && !self.anon_consts.is_empty()
    }
    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut ullbc_ast::ExprBody) {
        for block_id in body.body.indices() {
            let Some(block) = body.body.get_mut(block_id) else {
                continue;
            };
            let mut new_calls: Vec<(LocalId, Call)> = vec![];
            block.dyn_visit_in_body_mut(|op: &mut Operand| {
                if let Operand::Const(c) = op
                    && let ConstantExprKind::Global(gref) = &mut c.kind
                    && let Some(initializer) = self.anon_consts.get(&gref.id)
                {
                    let return_place = body.locals.new_var(None, c.ty.clone());
                    new_calls.push((
                        return_place.as_local().unwrap(),
                        Call {
                            func: FnOperand::Regular(FnPtr::new(
                                FnPtrKind::Fun(FunId::Regular(*initializer)),
                                gref.generics.clone(),
                            )),
                            args: vec![],
                            dest: return_place.clone(),
                        },
                    ));
                    *op = Operand::Move(return_place);
                }
            });
            if !new_calls.is_empty() {
                // Move the current block out of the way.
                let block = mem::replace(&mut body.body[block_id], BlockData::new_unreachable());
                let mut next_block = body.body.push(block);
                // Each new block jumps to the previous one after completion
                for (local_id, call) in new_calls {
                    // Const eval mustn't unwind into runtime.
                    let unwind = body.body.push(BlockData::new_unreachable());
                    next_block = body.body.push(BlockData {
                        statements: vec![Statement::new(
                            Span::dummy(),
                            StatementKind::StorageLive(local_id),
                        )],
                        terminator: Terminator::new(
                            Span::dummy(),
                            TerminatorKind::Call {
                                call,
                                target: next_block,
                                on_unwind: unwind,
                            },
                        ),
                    });
                }
                // Instead of the current block, start evaluating the new bodies.
                body.body[block_id] = BlockData::new_goto(Span::dummy(), next_block);
            }
        }
    }
    fn finalize(&self, ctx: &mut TransformCtx) {
        for gid in self.anon_consts.keys() {
            ctx.translated.global_decls.remove(*gid);
        }
    }
}
