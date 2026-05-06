use super::super::ctx::UllbcPass;
use crate::{
    transform::{
        TransformCtx,
        ctx::{BodyTransformCtx, UllbcStatementTransformCtx},
    },
    ullbc_ast::*,
};

fn is_noop_destruct(glue: &FnPtr) -> bool {
    match glue.kind.as_ref() {
        FnPtrKind::Trait(tref, _, _) => matches!(
            &tref.kind,
            TraitRefKind::BuiltinOrAuto {
                builtin_data: BuiltinImplData::NoopDestruct,
                ..
            }
        ),
        _ => false,
    }
}

impl<'a> UllbcStatementTransformCtx<'a> {
    /// Transform a Drop to a Call that calls the drop_in_place method.
    /// If we cannot desugar this drop, we just leave it unchanged.
    fn transform_drop_to_call(&mut self, term: &mut Terminator) {
        if let TerminatorKind::Drop {
            kind: DropKind::Precise,
            place,
            fn_ptr,
            target,
            on_unwind,
        } = &mut term.kind
        {
            // check if this drop is noop
            if is_noop_destruct(fn_ptr) {
                term.kind = TerminatorKind::Goto { target: *target };
                return;
            }

            // assign `&raw mut place` to a new variable
            let drop_arg =
                self.raw_borrow_to_new_var(place.clone(), RefKind::Mut, Some("drop_arg".into()));

            let drop_ret = self.fresh_var(Some("drop_ret".into()), Ty::mk_unit());
            let call = Call {
                func: FnOperand::Regular(fn_ptr.clone()),
                args: Vec::from([Operand::Move(drop_arg)]),
                dest: drop_ret,
            };
            term.kind = TerminatorKind::Call {
                call,
                target: *target,
                on_unwind: *on_unwind,
            };
        }
    }
}

pub struct Transform;

impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.desugar_drops
    }
    fn transform_function(&self, ctx: &mut TransformCtx, decl: &mut FunDecl) {
        decl.transform_ullbc_terminators(ctx, |ctx, term| {
            ctx.transform_drop_to_call(term);
        });
    }
}
