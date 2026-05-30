use std::{collections::HashMap, mem};

use crate::transform::CowBox;
use crate::transform::{TransformCtx, ctx::UllbcPass};
use crate::ullbc_ast::*;

pub struct Transform {
    to_inline: HashMap<FunDeclId, FunDecl>,
}

impl Transform {
    pub fn new(ctx: &mut TransformCtx) -> CowBox<dyn UllbcPass> {
        let panic_name = Name::from_path(builtins::EXPLICIT_PANIC_NAME);
        let panic_terminator = TerminatorKind::Abort(AbortKind::Panic(Some(panic_name)));

        // Collect and remove the functions that we want to inline.
        let to_inline = ctx
            .translated
            .fun_decls
            .extract(|_, decl| {
                decl.body.as_unstructured().is_some_and(|body| {
                    // If the whole body is only a call to this specific panic function.
                    // FIXME: also check that the name of the function is `panic_cold_explicit`?
                    let is_local_panic_fn = body.body.len() == 1 && {
                        let block = &body.body[0];
                        block.statements.is_empty() && block.terminator.kind == panic_terminator
                    };
                    // The `anon_consts_to_call` pass already transformed references to anon consts
                    // into calls to their initializers so we only have to inline these.
                    let is_anon_const_initializer = decl
                        .is_global_initializer
                        .and_then(|gid| ctx.translated.global_decls.get(gid))
                        .is_some_and(|gdecl| matches!(gdecl.global_kind, GlobalKind::AnonConst));
                    let is_vec_construction_fn = decl.item_meta.lang_item.as_deref()
                        == Some(builtins::BOX_ASSUME_INIT_INTO_VEC_UNSAFE);
                    is_local_panic_fn
                        || (is_anon_const_initializer && !ctx.options.raw_consts)
                        || (is_vec_construction_fn && ctx.options.treat_box_as_builtin)
                })
            })
            .collect();

        CowBox::Owned(Box::new(Transform { to_inline }))
    }
}
impl UllbcPass for Transform {
    fn should_run(&self, _options: &crate::options::TranslateOptions) -> bool {
        !self.to_inline.is_empty()
    }
    fn apply_preceding_passes(&mut self, ctx: &mut TransformCtx, passes: &[CowBox<dyn UllbcPass>]) {
        for decl in self.to_inline.values_mut() {
            for pass in passes {
                pass.transform_item(ctx, ItemRefMut::Fun(decl));
            }
        }
    }
    fn transform_body(&self, _ctx: &mut TransformCtx, outer_body: &mut ullbc_ast::ExprBody) {
        for block_id in outer_body.body.indices() {
            let Some(block) = outer_body.body.get_mut(block_id) else {
                continue;
            };
            let TerminatorKind::Call {
                call: Call { func, args, dest },
                target,
                on_unwind,
            } = &mut block.terminator.kind
            else {
                continue;
            };
            let target = *target;
            let on_unwind = *on_unwind;
            let dest_place = dest.clone();
            let args = args.clone();
            let FnOperand::Regular(fn_ptr) = &func else {
                continue;
            };
            let FnPtrKind::Fun(FunId::Regular(fun_id)) = fn_ptr.kind.as_ref() else {
                continue;
            };
            let Some(initializer) = self.to_inline.get(fun_id) else {
                continue;
            };
            let span = initializer.item_meta.span;
            let Some(inner_body) = initializer.body.as_unstructured() else {
                continue;
            };

            // We inline the required body by shifting its local ids and block ids
            // and adding its blocks to the outer body. The inner body's return
            // local becomes a normal local that we can read from. We redirect some
            // gotos so that the inner body is executed before the current block.
            let mut inner_body = {
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
                inner_body.substitute(&fn_ptr.generics)
            };

            let return_local = outer_body.locals.locals.next_idx();
            inner_body.dyn_visit_in_body_mut(|l: &mut LocalId| {
                *l += return_local;
            });
            outer_body
                .locals
                .locals
                .extend(mem::take(&mut inner_body.locals.locals));

            // The inner body assumes the return and arg places are live; allocate them, and
            // initialize the args.
            inner_body.body[0].statements.splice(
                0..0,
                [StatementKind::StorageLive(return_local)]
                    .into_iter()
                    .chain(args.into_iter().enumerate().flat_map(|(i, arg)| {
                        let arg_local = return_local + i + 1;
                        let arg_place = outer_body.locals.place_for_var(arg_local);
                        [
                            StatementKind::StorageLive(arg_local),
                            StatementKind::Assign(arg_place, Rvalue::Use(arg)),
                        ]
                    }))
                    .map(|kind| Statement::new(span, kind)),
            );

            let mut final_block = BlockData::new_goto(span, target);

            // The inner body will write to `return_place`, but the outer body expects the value at
            // `dest_place`.
            let return_place = outer_body.locals.place_for_var(return_local);
            final_block.statements.push(Statement::new(
                span,
                StatementKind::Assign(dest_place, Rvalue::Use(Operand::Move(return_place))),
            ));
            let final_block = outer_body.body.push(final_block);

            // Shift all block ids in the inner body and point return/unwind to where they should.
            let start_block = outer_body.body.next_idx();
            inner_body.dyn_visit_in_body_mut(|b: &mut BlockId| {
                *b += start_block;
            });
            inner_body
                .body
                .dyn_visit_in_body_mut(|t: &mut Terminator| match t.kind {
                    TerminatorKind::Return => {
                        t.kind = TerminatorKind::Goto {
                            target: final_block,
                        };
                    }
                    TerminatorKind::UnwindResume => {
                        t.kind = TerminatorKind::Goto { target: on_unwind };
                    }
                    _ => (),
                });
            // At the end of the current block, start evaluating the inner body.
            outer_body.body[block_id].terminator.kind = TerminatorKind::Goto {
                target: start_block,
            };
            // Add the blocks for the inner body.
            outer_body.body.extend(inner_body.body);
        }
    }
}
