//! The MIR code often contains variables with type `Never`, and we want to get
//! rid of those. We proceed in two steps. First, we remove the instructions
//! `drop(v)` where `v` has type `Never` (it can happen - this module does the
//! filtering). Then, we filter the unused variables ([crate::remove_unused_locals]).

use crate::formatter::Formatter;
use crate::llbc_ast::*;
use crate::meta::combine_meta;
use crate::translate_ctx::TransCtx;
use crate::types::*;
use crate::ullbc_ast::{iter_function_bodies, iter_global_bodies};
use std::iter::FromIterator;

struct Visitor<'a, 'tcx, 'ctx> {
    _ctx: &'a TransCtx<'tcx, 'ctx>,
}

impl<'a, 'tcx, 'ctx> Visitor<'a, 'tcx, 'ctx> {
    fn update_raw_statement(&mut self, st: &mut RawStatement) {
        match st {
            RawStatement::Sequence(
                box Statement {
                    content: RawStatement::Assign(dest, Rvalue::Discriminant(p)),
                    meta: meta1,
                },
                box st2,
            ) => {
                // The destination should be a variable
                assert!(dest.projection.is_empty());

                // Take st2
                let st2 = std::mem::replace(
                    st2,
                    Statement {
                        content: RawStatement::Nop,
                        meta: st2.meta,
                    },
                );

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
                        e,
                    )
                }));

                let switch = RawStatement::Switch(Switch::Match(p.clone(), targets, otherwise));

                // Add the next statement if there is one
                *st = if let Some(st3) = st3_opt {
                    let meta = combine_meta(meta1, &meta2);
                    let switch = Statement {
                        meta,
                        content: switch,
                    };
                    new_sequence(switch, st3).content
                } else {
                    switch
                };
            }
            RawStatement::Assign(_, Rvalue::Discriminant(_)) => {
                // We failed to remove a [Discriminant]
                unreachable!();
            }
            _ => (),
        }
    }
}

impl<'a, 'tcx, 'ctx> MutTypeVisitor for Visitor<'a, 'tcx, 'ctx> {}
impl<'a, 'tcx, 'ctx> MutExprVisitor for Visitor<'a, 'tcx, 'ctx> {}
impl<'a, 'tcx, 'ctx> MutAstVisitor for Visitor<'a, 'tcx, 'ctx> {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}

    fn visit_raw_statement(&mut self, st: &mut RawStatement) {
        self.update_raw_statement(st);

        // Visit again, to make sure we transform the branches and
        // the next statement, in case we updated, or to update the
        // sub-statements, in case we didn't perform any updates.
        self.default_visit_raw_statement(st);
    }
}

/// `fmt_ctx` is used for pretty-printing purposes.
pub fn transform(ctx: &TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to remove [ReadDiscriminant] occurrences in decl: {name}:\n{}",
            ctx.format_object(&*b)
        );

        let mut visitor = Visitor { _ctx: ctx };
        visitor.visit_statement(&mut b.body);
    }
}
