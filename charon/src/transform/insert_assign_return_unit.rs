//! When the function's return type is unit, the generated MIR doesn't
//! set the return value to `()`. This can be a concern: in the case
//! of AENEAS, it means the return variable contains ⊥ upon returning.
//! For this reason, when the function has return type unit, we insert
//! an extra assignment just before returning.

use crate::expressions::*;
use crate::llbc_ast::{ExprBody, FunDecl, GlobalDecl, RawStatement, Statement};
use crate::transform::TransformCtx;
use crate::types::*;
use crate::values::*;

use super::ctx::LlbcPass;

fn transform_st(st: &mut Statement) -> Option<Vec<Statement>> {
    if let RawStatement::Return = &mut st.content {
        let ret_place = Place {
            var_id: VarId::new(0),
            projection: Projection::new(),
        };
        let unit_value = Rvalue::Aggregate(
            AggregateKind::Adt(TypeId::Tuple, None, GenericArgs::empty()),
            Vec::new(),
        );
        let assign_st = Statement::new(st.span, RawStatement::Assign(ret_place, unit_value));
        let ret_st = Statement::new(st.span, RawStatement::Return);
        st.content = RawStatement::Sequence(Box::new(assign_st), Box::new(ret_st));
    };
    None
}

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_function(&self, ctx: &mut TransformCtx, decl: &mut FunDecl) {
        if decl.signature.output.is_unit() {
            self.transform_body(ctx, decl.body.as_mut().unwrap())
        }
    }
    fn transform_global(&self, ctx: &mut TransformCtx, decl: &mut GlobalDecl) {
        if decl.ty.is_unit() {
            self.transform_body(ctx, decl.body.as_mut().unwrap())
        }
    }
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, body: &mut ExprBody) {
        body.body.transform(&mut transform_st);
    }
}
