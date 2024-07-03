//! The MIR code often contains variables with type `Never`, and we want to get
//! rid of those. We proceed in two steps. First, we remove the instructions
//! `drop(v)` where `v` has type `Never` (it can happen - this module does the
//! filtering). Then, we filter the unused variables ([crate::remove_unused_locals]).

use crate::ast::*;
use crate::deps_errors::register_error_or_panic;
use crate::llbc_ast::*;
use crate::transform::TransformCtx;
use derive_visitor::visitor_enter_fn_mut;
use derive_visitor::DriveMut;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};

use super::ctx::LlbcPass;

pub struct Transform;
impl Transform {
    fn update_statement(ctx: &mut TransformCtx<'_>, st: &mut Statement) {
        let RawStatement::Sequence(seq) = &mut st.content else {
            return;
        };
        // Iterate through the statements.
        for i in 0..seq.len() {
            let suffix = &mut seq[i..];
            if let [Statement {
                content: RawStatement::Assign(dest, Rvalue::Discriminant(p, adt_id)),
                span: span1,
            }, rest @ ..] = suffix
            {
                // The destination should be a variable
                assert!(dest.projection.is_empty());

                // Lookup the type of the scrutinee
                let variants = match ctx.translated.type_decls.get(*adt_id) {
                    // This can happen if there was an error while extracting the definitions
                    None => None,
                    Some(d) => {
                        match &d.kind {
                            TypeDeclKind::Struct(_)
                            | TypeDeclKind::Opaque
                            | TypeDeclKind::Alias(..) => {
                                // We shouldn't get there
                                register_error_or_panic!(
                                    ctx,
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
                    // `Nop` the discriminant read.
                    assert!(ctx.has_errors());
                    seq[i].content = RawStatement::Nop;
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
                                switch.to_switch_int()
                            else {
                                unreachable!()
                            };
                            assert!(op_p.projection.is_empty() && op_p.var_id == dest.var_id);

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
                                                    register_error_or_panic!(
                                                        ctx,
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

                            // Replace the old switch with a match.
                            Switch::Match(p.clone(), targets, otherwise)
                        });
                        // `Nop` the discriminant read.
                        seq[i].content = RawStatement::Nop;
                    }
                    _ => {
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
                        seq[i].content =
                            RawStatement::Switch(Switch::Match(p.clone(), targets, None))
                    }
                }
            }
        }
    }
}

impl LlbcPass for Transform {
    fn transform_body(&self, ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        b.body
            .drive_mut(&mut visitor_enter_fn_mut(|st: &mut Statement| {
                Transform::update_statement(ctx, st);
            }));
    }
}
