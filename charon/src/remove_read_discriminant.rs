//! The MIR code often contains variables with type `Never`, and we want to get
//! rid of those. We proceed in two steps. First, we remove the instructions
//! `drop(v)` where `v` has type `Never` (it can happen - this module does the
//! filtering). Then, we filter the unused variables ([crate::remove_unused_locals]).

use take_mut::take;

use crate::expressions::*;
use crate::formatter::Formatter;
use crate::llbc_ast::*;
use crate::meta::combine_meta;
use crate::translate_ctx::TransCtx;
use crate::types::*;
use crate::ullbc_ast::{iter_function_bodies, iter_global_bodies};
use std::iter::FromIterator;

/*struct Visitor<'a, 'tcx, 'ctx> {
    ctx: &'a TransCtx<'tcx, 'ctx>,
}

impl<'a, 'tcx, 'ctx> MutTypeVisitor for Visitor<'a, 'tcx, 'ctx> {}
impl<'a, 'tcx, 'ctx> MutExprVisitor for Visitor<'a, 'tcx, 'ctx> {}
impl<'a, 'tcx, 'ctx> MutAstVisitor for Visitor<'a, 'tcx, 'ctx> {
    fn visit_raw_statement(&mut self, st: &mut RawStatement) {
        match st {
            RawStatement::Sequence(st1, st2) => {
                if st1.content.is_assign() {
                    let (_, rv) = st1.content.as_assign();
                    if rv.is_discriminant() {
                        let (dest, rv) = st1.content.to_assign();
                        let p = rv.to_discriminant();

                        // The destination should be a variable
                        assert!(dest.projection.is_empty());

                        // A discriminant read must be immediately followed by a switch int.
                        // Note that it may be contained in a sequence, of course.
                        let (meta, switch, st3_opt) = match st2.content {
                            RawStatement::Sequence(st2, st3) => {
                                (st2.meta, st2.content.to_switch(), Some(*st3))
                            }
                            RawStatement::Switch(switch) => (st2.meta, switch, None),
                            _ => unreachable!(),
                        };
                        let (op, int_ty, targets, otherwise) = switch.to_switch_int();
                        assert!(int_ty.is_isize());
                        // The operand should be a [Move] applied to the variable `dest`
                        let op_p = op.to_move();
                        assert!(op_p.projection.is_empty() && op_p.var_id == dest.var_id);

                        let targets = Vec::from_iter(targets.into_iter().map(|(v, e)| {
                            (
                                Vec::from_iter(
                                    v.into_iter()
                                        .map(|x| VariantId::Id::new(*x.as_isize() as usize)),
                                ),
                                transform_st(ctx, stack, e),
                            )
                        }));
                        let otherwise = Box::new(transform_st(ctx, stack, *otherwise));
                        let switch = RawStatement::Switch(Switch::Match(p, targets, otherwise));

                        // Add the next statement if there is one
                        if let Some(st3) = st3_opt {
                            let meta = combine_meta(&st1.meta, &meta);
                            let switch = Statement {
                                meta,
                                content: switch,
                            };
                            new_sequence(switch, st3).content
                        } else {
                            switch
                        }
                    } else {
                        let st1 = Box::new(transform_st(ctx, stack, *st1));
                        let st2 = Box::new(transform_st(ctx, stack, *st2));
                        RawStatement::Sequence(st1, st2)
                    }
                } else {
                    let st1 = Box::new(transform_st(ctx, stack, *st1));
                    let st2 = Box::new(transform_st(ctx, stack, *st2));
                    RawStatement::Sequence(st1, st2)
                }
            }
            _ => self.default_visit_raw_statement(st),
        }
    }
}*/

// TODO: use visitors
fn transform_st(ctx: &TransCtx, stack: usize, st: Statement) -> Statement {
    trace!(
        "- stack: {}\n- statement:\n{}",
        stack,
        st.fmt_with_ctx("", ctx)
    );
    let stack = stack + 1;

    let content = match st.content {
        RawStatement::Assign(p, rv) => {
            // Check that we never failed to remove a [Discriminant]
            if let Rvalue::Discriminant(_) = &rv {
                // Should have been filtered
                unreachable!();
            }
            RawStatement::Assign(p, rv)
        }
        RawStatement::FakeRead(p) => RawStatement::FakeRead(p),
        RawStatement::SetDiscriminant(p, vid) => RawStatement::SetDiscriminant(p, vid),
        RawStatement::Drop(p) => RawStatement::Drop(p),
        RawStatement::Assert(assert) => RawStatement::Assert(assert),
        RawStatement::Call(call) => RawStatement::Call(call),
        RawStatement::Panic => RawStatement::Panic,
        RawStatement::Return => RawStatement::Return,
        RawStatement::Break(i) => RawStatement::Break(i),
        RawStatement::Continue(i) => RawStatement::Continue(i),
        RawStatement::Nop => RawStatement::Nop,
        RawStatement::Switch(switch) => {
            let switch = match switch {
                Switch::If(op, st1, st2) => Switch::If(
                    op,
                    Box::new(transform_st(ctx, stack, *st1)),
                    Box::new(transform_st(ctx, stack, *st2)),
                ),
                Switch::SwitchInt(op, int_ty, targets, mut otherwise) => {
                    let targets = Vec::from_iter(
                        targets
                            .into_iter()
                            .map(|(v, e)| (v, transform_st(ctx, stack, e))),
                    );
                    *otherwise = transform_st(ctx, stack, *otherwise);
                    Switch::SwitchInt(op, int_ty, targets, otherwise)
                }
                Switch::Match(_, _, _) => {
                    // We shouldn't get there: this variant is introduced *during*
                    // this traversal
                    unreachable!();
                }
            };
            RawStatement::Switch(switch)
        }
        RawStatement::Loop(loop_body) => {
            RawStatement::Loop(Box::new(transform_st(ctx, stack, *loop_body)))
        }
        RawStatement::Sequence(
            box Statement {
                content: RawStatement::Assign(dest, Rvalue::Discriminant(p)),
                meta: meta1,
            },
            st2,
        ) => {
            // The destination should be a variable
            assert!(dest.projection.is_empty());

            // A discriminant read must be immediately followed by a switch int.
            // Note that it may be contained in a sequence, of course.
            let (meta2, switch, st3_opt) = match st2.content {
                RawStatement::Sequence(
                    box Statement {
                        content: RawStatement::Switch(switch),
                        meta: meta2,
                    },
                    box st3,
                ) => (meta2, switch, Some(st3)),
                RawStatement::Switch(switch) => (st2.meta, switch, None),
                _ => unreachable!(),
            };
            let Switch::SwitchInt(Operand::Move(op_p), int_ty, targets, otherwise) = switch
            else { unreachable!() };
            assert!(int_ty.is_isize());
            assert!(op_p.projection.is_empty() && op_p.var_id == dest.var_id);

            let targets = Vec::from_iter(targets.into_iter().map(|(v, e)| {
                (
                    Vec::from_iter(
                        v.into_iter()
                            .map(|x| VariantId::Id::new(*x.as_isize() as usize)),
                    ),
                    transform_st(ctx, stack, e),
                )
            }));
            let otherwise = Box::new(transform_st(ctx, stack, *otherwise));
            let switch = RawStatement::Switch(Switch::Match(p, targets, otherwise));

            // Add the next statement if there is one
            if let Some(st3) = st3_opt {
                let meta = combine_meta(&meta1, &meta2);
                let switch = Statement {
                    meta,
                    content: switch,
                };
                new_sequence(switch, st3).content
            } else {
                switch
            }
        }
        RawStatement::Sequence(st1, st2) => {
            let st1 = Box::new(transform_st(ctx, stack, *st1));
            let st2 = Box::new(transform_st(ctx, stack, *st2));
            RawStatement::Sequence(st1, st2)
        }
    };

    Statement::new(st.meta, content)
}

/// `fmt_ctx` is used for pretty-printing purposes.
pub fn transform(ctx: &TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to remove [ReadDiscriminant] occurrences in decl: {name}:\n{}",
            ctx.format_object(&*b)
        );

        // Compute the set of local variables
        take(&mut b.body, |body| transform_st(ctx, 0, body));
    }
}
