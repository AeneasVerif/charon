//! The MIR code often contains variables with type `Never`, and we want to get
//! rid of those. We proceed in two steps. First, we remove the instructions
//! `drop(v)` where `v` has type `Never` (it can happen - this module does the
//! filtering). Then, we filter the unused variables ([crate::remove_unused_locals]).

use crate::formatter::{Formatter, IntoFormatter};
use crate::llbc_ast::*;
use crate::meta::combine_meta;
use crate::translate_ctx::*;
use crate::types::*;
use std::collections::HashSet;
use std::iter::FromIterator;

struct Visitor<'a, 'tcx, 'ctx> {
    ctx: &'a mut TransCtx<'tcx, 'ctx>,
}

impl<'a, 'tcx, 'ctx> Visitor<'a, 'tcx, 'ctx> {
    fn update_statement(&mut self, st: &mut Statement) {
        match &mut st.content {
            RawStatement::Sequence(
                box Statement {
                    content: RawStatement::Assign(dest, Rvalue::Discriminant(p, adt_id)),
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

                let Switch::SwitchInt(Operand::Move(op_p), _int_ty, targets, otherwise) = switch
                else { unreachable!() };
                // Remark: the discriminant can be of any *signed* integer type
                // (`isize` of course, but also `i8`, etc.).
                assert!(op_p.projection.is_empty() && op_p.var_id == dest.var_id);

                let targets = Vec::from_iter(targets.into_iter().map(|(v, e)| {
                    (
                        Vec::from_iter(
                            v.into_iter()
                                .map(|x| VariantId::Id::new(x.as_int().unwrap() as usize)),
                        ),
                        e,
                    )
                }));
                // Filter the otherwise branch, if it is not necessary.
                use crate::id_vector::ToUsize;
                let covered_variants: HashSet<usize> =
                    targets.iter().fold(HashSet::new(), |mut hs, (ids, _)| {
                        ids.iter().for_each(|id| {
                            let _ = hs.insert(id.to_usize());
                        });
                        hs
                    });
                let covers_all = {
                    // Lookup the type of the scrutinee
                    match self.ctx.type_decls.get(*adt_id) {
                        None => {
                            // This can happen if there was an error while
                            // extracting the definitions
                            assert!(self.ctx.error_count > 0);
                            // For safety, we consider that not all the patterns
                            // were covered
                            false
                        }
                        Some(d) => {
                            match &d.kind {
                                TypeDeclKind::Struct(_) | TypeDeclKind::Opaque => {
                                    // We shouldn't get there
                                    register_error_or_panic!(
                                        self.ctx,
                                        st.meta.span.rust_span,
                                        "Unreachable case"
                                    );
                                    false
                                }
                                TypeDeclKind::Error(_) => false,
                                TypeDeclKind::Enum(variants) => {
                                    // Check that all the variants are covered
                                    variants
                                        .iter()
                                        .enumerate()
                                        .all(|(i, _)| covered_variants.contains(&i))
                                }
                            }
                        }
                    }
                };
                let otherwise = if covers_all { None } else { Some(otherwise) };

                let switch = RawStatement::Switch(Switch::Match(p.clone(), targets, otherwise));

                // Add the next statement if there is one
                st.content = if let Some(st3) = st3_opt {
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
            RawStatement::Assign(_, Rvalue::Discriminant(_, _)) => {
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

    fn visit_statement(&mut self, st: &mut Statement) {
        self.update_statement(st);

        // Visit again, to make sure we transform the branches and
        // the next statement, in case we updated, or to update the
        // sub-statements, in case we didn't perform any updates.
        self.default_visit_statement(st);
    }
}

pub fn transform(ctx: &mut TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    ctx.iter_bodies(funs, globals, |ctx, name, b| {
        let fmt_ctx = ctx.into_fmt();
        trace!(
            "# About to remove [ReadDiscriminant] occurrences in decl: {}:\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );

        let mut visitor = Visitor { ctx };
        visitor.visit_statement(&mut b.body);
    })
}
