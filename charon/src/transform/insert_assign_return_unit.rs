//! When the function's return type is unit, the generated MIR doesn't
//! set the return value to `()`. This can be a concern: in the case
//! of AENEAS, it means the return variable contains ⊥ upon returning.
//! For this reason, when the function has return type unit, we insert
//! an extra assignment just before returning.

use crate::llbc_ast::*;
use crate::transform::TransformCtx;

use super::ctx::LlbcPass;

fn transform_st(st: &mut Statement) -> Vec<Statement> {
    if let RawStatement::Return = &mut st.content {
        let ret_place = Place {
            var_id: VarId::new(0),
            projection: Projection::new(),
        };
        let unit_value = Rvalue::Aggregate(
            AggregateKind::Adt(TypeId::Tuple, None, None, GenericArgs::empty()),
            Vec::new(),
        );
        let assign_st = Statement::new(st.span, RawStatement::Assign(ret_place, unit_value));
        vec![assign_st]
    } else {
        Vec::new()
    }
}

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_function(
        &self,
        ctx: &mut TransformCtx,
        decl: &mut FunDecl,
        body: Result<&mut ExprBody, Opaque>,
    ) {
        if decl.signature.output.is_unit() {
            if let Ok(body) = body {
                self.transform_body(ctx, body)
            }
        }
    }
    fn transform_global(
        &self,
        ctx: &mut TransformCtx,
        decl: &mut GlobalDecl,
        body: Result<&mut ExprBody, Opaque>,
    ) {
        if decl.ty.is_unit() {
            if let Ok(body) = body {
                self.transform_body(ctx, body)
            }
        }
    }
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, body: &mut ExprBody) {
        body.body.transform(&mut transform_st);
    }
}
