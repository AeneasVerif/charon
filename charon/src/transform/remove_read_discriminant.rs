//! The MIR code often contains variables with type `Never`, and we want to get
//! rid of those. We proceed in two steps. First, we remove the instructions
//! `drop(v)` where `v` has type `Never` (it can happen - this module does the
//! filtering). Then, we filter the unused variables ([crate::remove_unused_locals]).

use crate::formatter::{Formatter, IntoFormatter};
use crate::llbc_ast::*;
use crate::meta::combine_span;
use crate::pretty::FmtWithCtx;
use crate::translate_ctx::*;
use crate::types::*;
use crate::values::{Literal, ScalarValue};
use itertools::Itertools;
use std::collections::{HashMap, HashSet};

struct Visitor<'a, 'ctx> {
    ctx: &'a mut TransformCtx<'ctx>,
}

impl<'a, 'ctx> Visitor<'a, 'ctx> {
    fn update_statement(&mut self, st: &mut Statement) {
        match &mut st.content {
            RawStatement::Sequence(
                box Statement {
                    content: RawStatement::Assign(dest, Rvalue::Discriminant(p, adt_id)),
                    span: span1,
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
                        span: st2.span,
                    },
                );

                // Lookup the type of the scrutinee
                let variants = match self.ctx.translated.type_decls.get(*adt_id) {
                    // This can happen if there was an error while extracting the definitions
                    None => None,
                    Some(d) => {
                        match &d.kind {
                            TypeDeclKind::Struct(_) | TypeDeclKind::Opaque => {
                                // We shouldn't get there
                                register_error_or_panic!(
                                    self.ctx,
                                    st.span.span.rust_span_data.span(),
                                    "Unreachable case"
                                );
                                None
                            }
                            TypeDeclKind::Error(_) => None,
                            TypeDeclKind::Enum(variants) => Some(variants),
                        }
                    }
                };
                let Some(variants) = variants else {
                    // An error occurred. We can't keep the `Rvalue::Discriminant` around so we
                    // `Nop` the whole statement sequence.
                    assert!(self.ctx.has_errors());
                    *st = Statement {
                        content: RawStatement::Nop,
                        span: st.span,
                    };
                    return;
                };

                // We look for a `SwitchInt` just after the discriminant read.
                // Note that it may be contained in a sequence, of course.
                let maybe_switch = match st2.content {
                    RawStatement::Sequence(
                        box Statement {
                            content: RawStatement::Switch(switch @ Switch::SwitchInt(..)),
                            span: span2,
                        },
                        box st3,
                    ) => Ok((span2, switch, Some(st3))),
                    RawStatement::Switch(switch @ Switch::SwitchInt(..)) => {
                        Ok((st2.span, switch, None))
                    }
                    _ => Err(st2),
                };

                match maybe_switch {
                    Ok((span2, switch, st3_opt)) => {
                        let Switch::SwitchInt(Operand::Move(op_p), _int_ty, targets, otherwise) =
                            switch
                        else {
                            unreachable!()
                        };
                        assert!(op_p.projection.is_empty() && op_p.var_id == dest.var_id);

                        // Convert between discriminants and variant indices. Remark: the discriminant can
                        // be of any *signed* integer type (`isize`, `i8`, etc.).
                        let discr_to_id: HashMap<ScalarValue, VariantId> = variants
                            .iter_indexed_values()
                            .map(|(id, variant)| (variant.discriminant, id))
                            .collect();
                        let mut covered_discriminants: HashSet<ScalarValue> = HashSet::default();
                        let targets = targets
                            .into_iter()
                            .map(|(v, e)| {
                                (
                                    v.into_iter()
                                        .filter_map(|discr| {
                                            covered_discriminants.insert(discr);
                                            discr_to_id.get(&discr).or_else(|| {
                                                register_error_or_panic!(
                                                    self.ctx,
                                                    st.span.span.rust_span_data.span(),
                                                    "Found incorrect discriminant {discr} for enum {adt_id}"
                                                );
                                                None
                                            })
                                        })
                                        .copied()
                                        .collect_vec(),
                                    e,
                                )
                            })
                            .collect_vec();
                        // Filter the otherwise branch if it is not necessary.
                        let covers_all = covered_discriminants.len() == discr_to_id.len();
                        let otherwise = if covers_all { None } else { Some(otherwise) };

                        let switch =
                            RawStatement::Switch(Switch::Match(p.clone(), targets, otherwise));

                        // Add the next statement if there is one
                        st.content = if let Some(st3) = st3_opt {
                            let span = combine_span(span1, &span2);
                            let switch = Statement {
                                span,
                                content: switch,
                            };
                            new_sequence(switch, st3).content
                        } else {
                            switch
                        };
                    }
                    Err(st2) => {
                        // The discriminant read is not followed by a `SwitchInt`. This can happen
                        // in optimized MIR. We replace `_x = Discr(_y)` with `match _y { 0 => { _x
                        // = 0 }, 1 => { _x = 1; }, .. }`.
                        let targets = variants
                            .iter_indexed_values()
                            .map(|(id, variant)| {
                                let value = variant.discriminant;
                                let int_ty = value.get_integer_ty();
                                let konst = ConstantExpr {
                                    value: RawConstantExpr::Literal(Literal::Scalar(value)),
                                    ty: Ty::Literal(LiteralTy::Integer(int_ty)),
                                };
                                let statement = Statement {
                                    span: *span1,
                                    content: RawStatement::Assign(
                                        dest.clone(),
                                        Rvalue::Use(Operand::Const(konst)),
                                    ),
                                };
                                (vec![id], statement)
                            })
                            .collect();
                        let switch = RawStatement::Switch(Switch::Match(p.clone(), targets, None));
                        let switch = Statement {
                            span: *span1,
                            content: switch,
                        };
                        st.content = new_sequence(switch, st2).content
                    }
                }
            }
            RawStatement::Assign(_, Rvalue::Discriminant(_, _)) => {
                // We failed to remove a [Discriminant]
                unreachable!();
            }
            _ => (),
        }
    }
}

impl<'a, 'ctx> MutTypeVisitor for Visitor<'a, 'ctx> {}
impl<'a, 'ctx> MutExprVisitor for Visitor<'a, 'ctx> {}
impl<'a, 'ctx> MutAstVisitor for Visitor<'a, 'ctx> {
    fn visit_statement(&mut self, st: &mut Statement) {
        self.update_statement(st);

        // Visit again, to make sure we transform the branches and
        // the next statement, in case we updated, or to update the
        // sub-statements, in case we didn't perform any updates.
        self.default_visit_statement(st);
    }
}

pub fn transform(ctx: &mut TransformCtx) {
    ctx.iter_structured_bodies(|ctx, name, b| {
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
