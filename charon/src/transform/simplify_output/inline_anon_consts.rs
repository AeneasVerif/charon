use std::{collections::HashMap, mem};

use crate::transform::CowBox;
use crate::transform::{TransformCtx, ctx::UllbcPass};
use crate::{ids::Generator, ullbc_ast::*};

pub struct Transform {
    anon_consts: HashMap<GlobalDeclId, FunDecl>,
}

impl Transform {
    pub fn new(ctx: &mut TransformCtx) -> CowBox<dyn UllbcPass> {
        // Map each anon const id to its initializer, and remove both from `translated`.
        let anon_consts = ctx
            .translated
            .global_decls
            .extract(|_, gdecl| matches!(gdecl.global_kind, GlobalKind::AnonConst))
            .filter_map(|(id, gdecl)| {
                let fdecl = ctx.translated.fun_decls.remove(gdecl.init)?;
                let _ = fdecl.body.as_unstructured()?;
                Some((id, fdecl))
            })
            .collect();
        CowBox::Owned(Box::new(Transform { anon_consts }))
    }
}
impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        !options.raw_consts && !self.anon_consts.is_empty()
    }
    fn apply_preceding_passes(&mut self, ctx: &mut TransformCtx, passes: &[CowBox<dyn UllbcPass>]) {
        for decl in self.anon_consts.values_mut() {
            for pass in passes {
                pass.transform_item(ctx, ItemRefMut::Fun(decl));
            }
        }
    }
    fn transform_body(&self, _ctx: &mut TransformCtx, outer_body: &mut ullbc_ast::ExprBody) {
        for block_id in outer_body.body.indices() {
            // Subtle: This generator must be managed to correctly track the indices that will
            // be generated when pushing onto `outer_body.body`.
            let mut bid_generator: Generator<BlockId> =
                Generator::new_with_init_value(outer_body.body.next_idx());
            let start_new_bodies = bid_generator.next_id();
            let Some(block) = outer_body.body.get_mut(block_id) else {
                continue;
            };
            let mut new_blocks = vec![];
            block.dyn_visit_in_body_mut(|op: &mut Operand| {
                if let Operand::Const(c) = op
                    && let ConstantExprKind::Global(gref) = &mut c.kind
                    && let Some(initializer) = self.anon_consts.get(&gref.id)
                    && let Some(inner_body) = initializer.body.as_unstructured()
                {
                    // We inline the required body by shifting its local ids and block ids
                    // and adding its blocks to the outer body. The inner body's return
                    // local becomes a normal local that we can read from. We redirect some
                    // gotos so that the inner body is executed before the current block.
                    let mut inner_body = inner_body.clone();
                    let inner_bound = inner_body.bound_body_regions;

                    // Shift all the body regions in the inner body BEFORE substitution,
                    // so that we only shift the inner body's own regions.
                    inner_body.dyn_visit_mut(|r: &mut Region| {
                        if let Region::Body(v) = r {
                            *v += outer_body.bound_body_regions;
                        }
                    });
                    outer_body.bound_body_regions += inner_bound;

                    // Now substitute generics. This may inject outer-body Region::Body
                    // IDs, which is correct since they don't need shifting.
                    let mut inner_body = inner_body.substitute(&gref.generics);

                    // The init function of a global assumes the return place is live;
                    // this is not the case once we inline it
                    inner_body.body[0].statements.insert(
                        0,
                        Statement::new(Span::dummy(), StatementKind::StorageLive(LocalId::ZERO)),
                    );

                    let return_local = outer_body.locals.locals.next_idx();
                    inner_body.dyn_visit_in_body_mut(|l: &mut LocalId| {
                        *l += return_local;
                    });

                    let start_block = bid_generator.next_id();
                    bid_generator.advance(inner_body.body.len());
                    let end_block = bid_generator.next_id();
                    inner_body.dyn_visit_in_body_mut(|b: &mut BlockId| {
                        *b += start_block;
                    });
                    // Make all returns point to `end_block`. This block doesn't exist yet,
                    // it will either be the start block of another inner body, or the
                    // current outer block that we'll push at the end.
                    inner_body.body.dyn_visit_in_body_mut(|t: &mut Terminator| {
                        if let TerminatorKind::Return = t.kind {
                            t.kind = TerminatorKind::Goto { target: end_block };
                        }
                    });

                    outer_body
                        .locals
                        .locals
                        .extend(inner_body.locals.locals.into_iter());
                    new_blocks.extend(inner_body.body);
                    *op = Operand::Move(outer_body.locals.place_for_var(return_local));
                }
            });
            if !new_blocks.is_empty() {
                // Instead of the current block, start evaluating the new bodies.
                let block =
                    mem::replace(block, BlockData::new_goto(Span::dummy(), start_new_bodies));
                // Add the new blocks. They've been set up so that each new inner body
                // returns to what follows it in the sequence. Hence the last added body
                // points to the not-yet-existing block at `start_new_bodies`
                outer_body.body.extend(new_blocks.into_iter());
                // Push the current block to be executed after the newly-added ones.
                outer_body.body.push(block);
            }
        }
    }
}
