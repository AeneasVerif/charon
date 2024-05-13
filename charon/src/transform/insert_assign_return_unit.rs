//! When the function's return type is unit, the generated MIR doesn't
//! set the return value to `()`. This can be a concern: in the case
//! of AENEAS, it means the return variable contains ⊥ upon returning.
//! For this reason, when the function has return type unit, we insert
//! an extra assignment just before returning.

use crate::expressions::*;
use crate::formatter::{Formatter, IntoFormatter};
use crate::llbc_ast::{
    ExprBody, FunDecl, GlobalDecl, RawStatement, Statement,
};
use crate::names::Name;
use crate::translate_ctx::TransCtx;
use crate::types::*;
use crate::values::*;

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
        let assign_st = Statement::new(st.meta, RawStatement::Assign(ret_place, unit_value));
        let ret_st = Statement::new(st.meta, RawStatement::Return);
        st.content = RawStatement::Sequence(Box::new(assign_st), Box::new(ret_st));
    };
    None
}

fn transform_body(ctx: &TransCtx, name: &Name, body: &mut Option<ExprBody>) {
    let ctx = ctx.into_fmt();
    if let Some(b) = body.as_mut() {
        trace!(
            "About to insert assign and return unit in decl: {}:\n{}",
            name.fmt_with_ctx(&ctx),
            ctx.format_object(&*b)
        );
        b.body.transform(&mut transform_st);
    }
}

fn transform_function(ctx: &mut TransCtx, def: &mut FunDecl) {
    if def.signature.output.is_unit() {
        ctx.with_def_id(def.rust_id, |ctx| {
            transform_body(ctx, &def.name, &mut def.body)
        });
    }
}
fn transform_global(ctx: &mut TransCtx, def: &mut GlobalDecl) {
    if def.ty.is_unit() {
        ctx.with_def_id(def.rust_id, |ctx| {
            transform_body(ctx, &def.name, &mut def.body)
        });
    }
}

pub fn transform(ctx: &mut TransCtx) {
    ctx.with_mut_structured_fun_decls(|ctx, fun_decls| {
        fun_decls
            .iter_mut()
            .for_each(|d| transform_function(ctx, d));
    });
    ctx.with_mut_structured_global_decls(|ctx, global_decls| {
        global_decls
            .iter_mut()
            .for_each(|d| transform_global(ctx, d));
    });
}
