//! The way to match on enums in MIR is in two steps: first read the discriminant, then switch on
//! the resulting integer. This pass records the enum place as the switch scrutinee and replaces
//! the integer cases with symbolic enum discriminants.
use itertools::Itertools;
use std::collections::{HashMap, HashSet};

use crate::formatter::IntoFormatter;
use crate::llbc_ast::*;
use crate::name_matcher::NamePattern;
use crate::pretty::FmtWithCtx;
use crate::transform::TransformCtx;
use crate::transform::ctx::LlbcPass;
use crate::{errors::register_error, transform::CowBox};

pub struct Transform {
    discriminant_intrinsics: HashSet<FunDeclId>,
}

impl Transform {
    fn update_block(&self, ctx: &mut TransformCtx, block: &mut Block) {
        // Iterate through the statements.
        for i in 0..block.statements.len() {
            let suffix = &mut block.statements[i..];
            match suffix {
                [
                    Statement {
                        kind: StatementKind::Assign(dest, Rvalue::Discriminant(p)),
                        ..
                    },
                    rest @ ..,
                ] => {
                    // The destination should be a variable
                    assert!(dest.is_local());
                    let TyKind::Adt(tdecl_ref) = p.ty().kind() else {
                        continue;
                    };

                    // Lookup the type of the scrutinee
                    let tkind = ctx.translated.type_decls.get(tdecl_ref.id).map(|x| &x.kind);
                    let Some(TypeDeclKind::Enum(variants)) = tkind else {
                        match tkind {
                            // This can happen if the type was declared as invisible or opaque.
                            None | Some(TypeDeclKind::Opaque) => {
                                let name = ctx.translated.item_name(tdecl_ref.id);
                                register_error!(
                                    ctx,
                                    block.span,
                                    "reading the discriminant of an opaque enum. \
                                    Add `--include {}` to the `charon` arguments \
                                    to translate this enum.",
                                    name.with_ctx(&ctx.into_fmt())
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
                        block.statements[i].kind = StatementKind::Error(
                            "error reading the discriminant of this type".to_owned(),
                        );
                        return;
                    };

                    // We look for a switch on the temporary just after the discriminant read.
                    match rest {
                        [
                            Statement {
                                kind: StatementKind::Switch { data, branches },
                                ..
                            },
                            ..,
                        ] if let SwitchScrutinee::Value(Operand::Move(op_p)) = &data.scrutinee
                            && op_p.is_local()
                            && op_p.local_id() == dest.local_id() =>
                        {
                            data.scrutinee = SwitchScrutinee::Discriminant(p.clone());

                            // Convert between discriminants and variant indices. Remark: the discriminant can
                            // be of any *signed* integer type (`isize`, `i8`, etc.).
                            let discr_to_id: HashMap<Literal, VariantId> = variants
                                .iter_enumerated()
                                .map(|(id, variant)| (variant.discriminant.clone(), id))
                                .collect();

                            let mut covered_discriminants: HashSet<Literal> = HashSet::default();
                            for (value, _) in &mut data.branches {
                                if let ConstantExprKind::Literal(discr) = value.kind()
                                    && let Some(variant_id) = discr_to_id.get(discr).copied()
                                {
                                    covered_discriminants.insert(discr.clone());
                                    *value = ConstantExpr::new(
                                        ConstantExprKind::Discriminant(
                                            tdecl_ref.clone(),
                                            variant_id,
                                        ),
                                        value.ty().clone(),
                                    );
                                } else {
                                    register_error!(
                                        ctx,
                                        block.span,
                                        "Found incorrect discriminant {value} for enum {}",
                                        tdecl_ref.id
                                    );
                                }
                            }

                            // The fallback is unnecessary if the explicit cases cover every
                            // variant.
                            if covered_discriminants.len() == discr_to_id.len() {
                                let fallback_id = data
                                    .fallback
                                    .take()
                                    .expect("MIR switches always have a fallback branch");
                                // Remove the fallback branch if nothing else points to it.
                                if !data
                                    .branches
                                    .iter()
                                    .map(|(_, branch_id)| *branch_id)
                                    .contains(&fallback_id)
                                {
                                    assert_eq!(fallback_id.index(), branches.len() - 1);
                                    branches.pop();
                                }
                            }
                            // `Nop` the discriminant read.
                            block.statements[i].kind = StatementKind::Nop;
                        }
                        _ => {
                            // The discriminant read is not followed by a switch on its result. This
                            // can happen in optimized MIR.
                            continue;
                        }
                    }
                }
                // Replace calls of `core::intrinsics::discriminant_value` on a known enum with the
                // appropriate MIR.
                [
                    Statement {
                        kind: StatementKind::Call { call, .. },
                        ..
                    },
                    ..,
                ] if let FnOperand::Regular(fn_ptr) = &call.func
                        && let FnPtrKind::Fun(FunId::Regular(fun_id)) = fn_ptr.kind.as_ref()
                        // Detect a call to the intrinsic...
                        && self.discriminant_intrinsics.contains(fun_id)
                        // passing it a reference.
                        && let Operand::Move(p) = &call.args[0]
                        && let TyKind::Ref(_, sub_ty, _) = p.ty().kind() =>
                {
                    let p = p.clone().project(ProjectionElem::Deref, sub_ty.clone());
                    block.statements[i].kind =
                        StatementKind::Assign(call.dest.clone(), Rvalue::Discriminant(p.clone()))
                }
                _ => {}
            }
        }
    }
}

const DISCRIMINANT_INTRINSIC: &str = "core::intrinsics::discriminant_value";

impl Transform {
    pub fn new(ctx: &mut TransformCtx) -> CowBox<dyn LlbcPass> {
        let pat = NamePattern::parse(DISCRIMINANT_INTRINSIC).unwrap();
        // There can be many if we're in mono mode.
        let discriminant_intrinsics = ctx
            .translated
            .item_names
            .iter()
            .filter(|(_, name)| pat.matches(&ctx.translated, name))
            .filter_map(|(id, _)| id.as_fun())
            .copied()
            .collect();
        CowBox::Owned(Box::new(Transform {
            discriminant_intrinsics,
        }))
    }
}

impl LlbcPass for Transform {
    fn transform_body(&self, ctx: &mut TransformCtx, body: &mut llbc_ast::ExprBody) {
        body.body.visit_blocks_bwd(|block: &mut Block| {
            self.update_block(ctx, block);
        })
    }
}
