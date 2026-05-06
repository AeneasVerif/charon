use crate::transform::TransformCtx;
use crate::transform::ctx::FusedUllbcPass;
use crate::ullbc_ast::*;

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

fn is_trivial_drop(stmt: &Terminator) -> bool {
    matches!(
        &stmt.kind,
        TerminatorKind::Drop { fn_ptr, .. }
            if is_noop_destruct(fn_ptr)
    )
}

pub struct Transform;
impl FusedUllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut ullbc_ast::ExprBody) {
        for block in &mut body.body {
            if is_trivial_drop(&block.terminator)
                && let TerminatorKind::Drop { target, .. } = &block.terminator.kind
            {
                block.terminator.kind = TerminatorKind::Goto { target: *target };
            }
        }
    }
}
