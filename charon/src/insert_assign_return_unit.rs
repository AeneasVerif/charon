//! When the function's return type is unit, the generated MIR doesn't
//! set the return value to `()`. This can be a concern: in the case
//! of AENEAS, it means the return variable contains ⊥ upon returning.
//! For this reason, when the function has return type unit, we insert
//! an extra assignment just before returning.

use crate::expressions::*;
use crate::formatter::Formatter;
use crate::llbc_ast::{
    ExprBody, FunDecl, FunDecls, GlobalDecl, GlobalDecls, RawStatement, Statement,
};
use crate::names::Name;
use crate::translate_ctx::TransCtx;
use crate::values::*;

fn transform_st(st: &mut Statement) -> Vec<Statement> {
    if let RawStatement::Return = &mut st.content {
        let ret_place = Place {
            var_id: VarId::Id::new(0),
            projection: Projection::new(),
        };
        let unit_value = Rvalue::Aggregate(AggregateKind::Tuple, Vec::new());
        let assign_st = Statement::new(st.meta, RawStatement::Assign(ret_place, unit_value));
        let ret_st = Statement::new(st.meta, RawStatement::Return);
        st.content = RawStatement::Sequence(Box::new(assign_st), Box::new(ret_st));
    };
    Vec::new()
}

fn transform_body(ctx: &TransCtx, name: &Name, body: &mut Option<ExprBody>) {
    if let Some(b) = body.as_mut() {
        trace!(
            "About to insert assign and return unit in decl: {name}:\n{}",
            ctx.format_object(&*b)
        );
        b.body.transform(&mut transform_st);
    }
}

fn transform_function(ctx: &TransCtx, def: &mut FunDecl) {
    if def.signature.output.is_unit() {
        transform_body(ctx, &def.name, &mut def.body);
    }
}
fn transform_global(ctx: &TransCtx, def: &mut GlobalDecl) {
    if def.ty.is_unit() {
        transform_body(ctx, &def.name, &mut def.body);
    }
}

pub fn transform(ctx: &TransCtx, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    funs.iter_mut().for_each(|d| transform_function(ctx, d));
    globals.iter_mut().for_each(|d| transform_global(ctx, d));
}
