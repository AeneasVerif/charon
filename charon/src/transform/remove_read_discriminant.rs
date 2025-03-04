//! The MIR code often contains variables with type `Never`, and we want to get
//! rid of those. We proceed in two steps. First, we remove the instructions
//! `drop(v)` where `v` has type `Never` (it can happen - this module does the
//! filtering). Then, we filter the unused variables ([crate::remove_unused_locals]).

use crate::errors::register_error;
use crate::formatter::IntoFormatter;
use crate::llbc_ast::*;
use crate::pretty::FmtWithCtx;
use crate::transform::TransformCtx;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};

use super::ctx::LlbcPass;

pub struct Transform;
impl Transform {
    fn update_block(ctx: &mut TransformCtx, block: &mut Block) {
        // Iterate through the statements.
        for i in 0..block.statements.len() {
            let suffix = &mut block.statements[i..];
            if let [Statement {
                content: RawStatement::Assign(dest, Rvalue::Discriminant(p, adt_id)),
                span: span1,
                ..
            }, rest @ ..] = suffix
            {
                // The destination should be a variable
                assert!(dest.is_local());

                // Lookup the type of the scrutinee
                let tkind = ctx.translated.type_decls.get(*adt_id).map(|x| &x.kind);
                let Some(TypeDeclKind::Enum(variants)) = tkind else {
                    match tkind {
                        // This can happen if the type was declared as invisible or opaque.
                        None | Some(TypeDeclKind::Opaque) => {
                            let name = ctx.translated.item_name(*adt_id).unwrap();
                            register_error!(
                                ctx,
                                block.span,
                                "reading the discriminant of an opaque enum. \
                                    Add `--include {}` to the `charon` arguments \
                                    to translate this enum.",
                                name.fmt_with_ctx(&ctx.into_fmt())
                            );
                        }
                        // Don't double-error
                        Some(TypeDeclKind::Error(..)) => {}
                        Some(_) => {
                            register_error!(
                                ctx,
                                block.span,
                                "reading the discriminant of a non-enum type"
                            );
                        }
                    }
                    block.statements[i].content = RawStatement::Error(
                        "error reading the discriminant of this type".to_owned(),
                    );
                    return;
                };

                // We look for a `SwitchInt` just after the discriminant read.
                match rest {
                    [Statement {
                        content:
                            RawStatement::Switch(switch @ Switch::SwitchInt(Operand::Move(_), ..)),
                        ..
                    }, ..] => {
                        // Convert between discriminants and variant indices. Remark: the discriminant can
                        // be of any *signed* integer type (`isize`, `i8`, etc.).
                        let discr_to_id: HashMap<ScalarValue, VariantId> = variants
                            .iter_indexed_values()
                            .map(|(id, variant)| (variant.discriminant, id))
                            .collect();

                        take_mut::take(switch, |switch| {
                            let (Operand::Move(op_p), _, targets, otherwise) =
                                switch.to_switch_int().unwrap()
                            else {
                                unreachable!()
                            };
                            assert!(op_p.is_local() && op_p.var_id() == dest.var_id());

                            let mut covered_discriminants: HashSet<ScalarValue> =
                                HashSet::default();
                            let targets = targets
                                .into_iter()
                                .map(|(v, e)| {
                                    (
                                        v.into_iter()
                                            .filter_map(|discr| {
                                                covered_discriminants.insert(discr);
                                                discr_to_id.get(&discr).or_else(|| {
                                                    register_error!(
                                                        ctx,
                                                        block.span,
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

                            // Replace the old switch with a match.
                            Switch::Match(p.clone(), targets, otherwise)
                        });
                        // `Nop` the discriminant read.
                        block.statements[i].content = RawStatement::Nop;
                    }
                    _ => {
                        // The discriminant read is not followed by a `SwitchInt`. This can happen
                        // in optimized MIR. We replace `_x = Discr(_y)` with `match _y { 0 => { _x
                        // = 0 }, 1 => { _x = 1; }, .. }`.
                        let targets = variants
                            .iter_indexed_values()
                            .map(|(id, variant)| {
                                let discr_value =
                                    Rvalue::Use(Operand::Const(variant.discriminant.to_constant()));
                                let statement = Statement::new(
                                    *span1,
                                    RawStatement::Assign(dest.clone(), discr_value),
                                );
                                (vec![id], statement.into_block())
                            })
                            .collect();
                        block.statements[i].content =
                            RawStatement::Switch(Switch::Match(p.clone(), targets, None))
                    }
                }
            }
        }
    }
}

impl LlbcPass for Transform {
    fn transform_body(&self, ctx: &mut TransformCtx, b: &mut ExprBody) {
        b.body.visit_blocks_bwd(|block: &mut Block| {
            Transform::update_block(ctx, block);
        });
    }
}
