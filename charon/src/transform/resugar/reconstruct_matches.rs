//! The way to match on enums in MIR is in two steps: first read the discriminant, then switch on
//! the resulting integer. This pass records the enum place as the switch scrutinee and replaces
//! the integer cases with symbolic enum discriminants.
use std::{
    collections::{HashMap, HashSet},
    mem,
};

use crate::formatter::IntoFormatter;
use crate::name_matcher::NamePattern;
use crate::pretty::FmtWithCtx;
use crate::transform::TransformCtx;
use crate::transform::ctx::UllbcPass;
use crate::ullbc_ast::*;
use crate::{errors::register_error, transform::CowBox};

pub struct Transform {
    discriminant_intrinsics: HashSet<FunDeclId>,
}

impl Transform {
    fn replace_mem_discriminant_call(&self, block: &mut BlockData) {
        if let TerminatorKind::Call { call, target, .. } = &block.terminator.kind
            && let FnOperand::Regular(fn_ptr) = &call.func
            && let FnPtrKind::Fun(FunId::Regular(fun_id)) = fn_ptr.kind.as_ref()
            && self.discriminant_intrinsics.contains(fun_id)
            && let [Operand::Move(p)] = call.args.as_slice()
            && let TyKind::Ref(_, sub_ty, _) = p.ty().kind()
        {
            let dest = call.dest.clone();
            let p = p.clone().project(ProjectionElem::Deref, sub_ty.clone());
            let target = *target;
            let mut statement = Statement::new(
                block.terminator.span,
                StatementKind::Assign(dest, Rvalue::Discriminant(p)),
            );
            statement.comments_before = mem::take(&mut block.terminator.comments_before);
            block.statements.push(statement);
            block.terminator.kind = TerminatorKind::Goto { target };
        }
    }

    fn reconstruct_match(&self, ctx: &mut TransformCtx, block: &mut BlockData) {
        let span = block.terminator.span;
        let TerminatorKind::Switch { data, .. } = &mut block.terminator.kind else {
            return;
        };
        let SwitchScrutinee::Value(Operand::Move(op_p)) = &data.scrutinee else {
            return;
        };
        // If the last statement is a discriminant read.
        let Some(last_st) = block.statements.last_mut() else {
            return;
        };
        let StatementKind::Assign(dest, Rvalue::Discriminant(p)) = &last_st.kind else {
            return;
        };
        assert!(dest.is_local()); // The destination should be a variable.
        if op_p != dest {
            return;
        }
        let scrut_ty = p.ty().clone();

        // Merge the two statements.
        data.scrutinee = SwitchScrutinee::Discriminant(p.clone());
        last_st.kind = StatementKind::Nop;

        // Lookup the type of the scrutinee.
        let TyKind::Adt(tdecl_ref) = scrut_ty.kind() else {
            return;
        };
        let tdecl_ref = tdecl_ref.clone();
        let adt_id = tdecl_ref.id;
        let tkind = ctx.translated.type_decls.get(adt_id).map(|x| &x.kind);
        let Some(TypeDeclKind::Enum(variants)) = tkind else {
            match tkind {
                // This can happen if the type was declared as invisible or opaque.
                None | Some(TypeDeclKind::Opaque) => {
                    let name = ctx.translated.item_name(adt_id);
                    register_error!(
                        ctx,
                        span,
                        "reading the discriminant of an opaque enum. \
                        Add `--include {}` to the `charon` arguments \
                        to translate this enum.",
                        name.with_ctx(&ctx.into_fmt())
                    );
                }
                // Don't double-error.
                Some(TypeDeclKind::Error(..)) => {}
                Some(_) => {
                    register_error!(ctx, span, "reading the discriminant of a non-enum type");
                }
            }
            return;
        };

        // Map from discriminants to variant indices. Remark: the discriminant can be of any
        // *signed* integer type (`isize`, `i8`, etc.).
        let discr_to_id: HashMap<Literal, VariantId> = variants
            .iter_enumerated()
            .map(|(id, variant)| (variant.discriminant.clone(), id))
            .collect();

        // Replace the branch values with discriminant constants.
        let mut covered_discriminants: HashSet<Literal> = HashSet::default();
        for (value, _) in &mut data.branches {
            if let ConstantExprKind::Literal(discr) = value.kind()
                && let Some(variant_id) = discr_to_id.get(discr).copied()
            {
                covered_discriminants.insert(discr.clone());
                *value = ConstantExpr::new(
                    ConstantExprKind::Discriminant(tdecl_ref.clone(), variant_id),
                    value.ty().clone(),
                );
            } else {
                register_error!(
                    ctx,
                    block.terminator.span,
                    "Found incorrect discriminant {value} for enum {adt_id}"
                );
            }
        }

        // Remove the fallback if the explicit cases cover every variant.
        if covered_discriminants.len() == discr_to_id.len() {
            data.fallback.take();
        }
    }
}

const DISCRIMINANT_INTRINSIC: &str = "core::intrinsics::discriminant_value";

impl Transform {
    pub fn new(ctx: &mut TransformCtx) -> CowBox<dyn UllbcPass> {
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

impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.reconstruct_matches
    }

    fn transform_body(&self, ctx: &mut TransformCtx, body: &mut ExprBody) {
        for block in &mut body.body {
            self.reconstruct_match(ctx, block);
            self.replace_mem_discriminant_call(block);
        }
    }
}
