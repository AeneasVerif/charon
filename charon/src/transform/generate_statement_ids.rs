//! Introduce a unique id for every statement.
use crate::ids::Generator;
use crate::llbc_ast::*;
use crate::transform::TransformCtx;

use super::ctx::LlbcPass;

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, b: &mut ExprBody) {
        let mut generator = Generator::new();
        b.body.visit_statements(|st: &mut Statement| {
            st.id = generator.fresh_id();
        });
    }
}
