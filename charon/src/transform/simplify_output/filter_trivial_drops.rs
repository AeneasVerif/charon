use crate::transform::TransformCtx;
use crate::transform::ctx::UllbcPass;
use crate::ullbc_ast::*;

fn is_trivial_drop(stmt: &Statement) -> bool {
    matches!(
        &stmt.kind,
        StatementKind::Drop(_, tref)
            if matches!(
                &tref.kind,
                TraitRefKind::BuiltinOrAuto { builtin_data: BuiltinImplData::NoopDestruct, .. }
            )
    )
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut ullbc_ast::ExprBody) {
        for block in &mut body.body {
            if block.statements.iter().any(is_trivial_drop) {
                block.statements.retain(|stmt| !is_trivial_drop(stmt));
            }
        }
    }
}
