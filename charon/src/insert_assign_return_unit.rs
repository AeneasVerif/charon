//! When the function's return type is unit, the generated MIR doesn't
//! set the return value to `()`. This can be a concern: in the case
//! of AENEAS, it means the return variable contains ⊥ upon returning.
//! For this reason, when the function has return type unit, we insert
//! an extra assignment just before returning.
use take_mut::take;

use crate::expressions::*;
use crate::llbc_ast::{
    CtxNames, ExprBody, FunDecl, FunDecls, GlobalDecl, GlobalDecls, RawStatement, Statement, Switch,
};
use crate::names::Name;
use crate::values::*;
use std::iter::FromIterator;

fn transform_st(mut st: Statement) -> Statement {
    st.content = match st.content {
        RawStatement::Return => {
            // The interesting case
            let ret_place = Place {
                var_id: VarId::Id::new(0),
                projection: Projection::new(),
            };
            let unit_value = Rvalue::Aggregate(AggregateKind::Tuple, Vec::new());
            let assign_st = Statement::new(st.meta, RawStatement::Assign(ret_place, unit_value));
            let ret_st = Statement::new(st.meta, RawStatement::Return);
            RawStatement::Sequence(Box::new(assign_st), Box::new(ret_st))
        }
        RawStatement::Assign(p, rv) => RawStatement::Assign(p, rv),
        RawStatement::FakeRead(p) => RawStatement::FakeRead(p),
        RawStatement::SetDiscriminant(p, vid) => RawStatement::SetDiscriminant(p, vid),
        RawStatement::Drop(p) => RawStatement::Drop(p),
        RawStatement::Assert(assert) => RawStatement::Assert(assert),
        RawStatement::Call(call) => RawStatement::Call(call),
        RawStatement::Panic => RawStatement::Panic,
        RawStatement::Break(i) => RawStatement::Break(i),
        RawStatement::Continue(i) => RawStatement::Continue(i),
        RawStatement::Nop => RawStatement::Nop,
        RawStatement::Switch(switch) => match switch {
            Switch::If(op, st1, st2) => {
                let st1 = Box::new(transform_st(*st1));
                let st2 = Box::new(transform_st(*st2));
                RawStatement::Switch(Switch::If(op, st1, st2))
            }
            Switch::SwitchInt(op, int_ty, targets, mut otherwise) => {
                let targets =
                    Vec::from_iter(targets.into_iter().map(|(v, e)| (v, transform_st(e))));
                *otherwise = transform_st(*otherwise);
                let switch = Switch::SwitchInt(op, int_ty, targets, otherwise);
                RawStatement::Switch(switch)
            }
            Switch::Match(op, targets, mut otherwise) => {
                let targets =
                    Vec::from_iter(targets.into_iter().map(|(v, e)| (v, transform_st(e))));
                *otherwise = transform_st(*otherwise);
                let switch = Switch::Match(op, targets, otherwise);
                RawStatement::Switch(switch)
            }
        },
        RawStatement::Loop(loop_body) => RawStatement::Loop(Box::new(transform_st(*loop_body))),
        RawStatement::Sequence(st1, st2) => {
            RawStatement::Sequence(Box::new(transform_st(*st1)), Box::new(transform_st(*st2)))
        }
    };
    st
}

fn transform_body<'ctx>(fmt_ctx: &CtxNames<'ctx>, name: &Name, body: &mut Option<ExprBody>) {
    if let Some(b) = body.as_mut() {
        trace!(
            "About to insert assign and return unit in decl: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
        take(&mut b.body, transform_st);
    }
}

fn transform_function<'ctx>(fmt_ctx: &CtxNames<'ctx>, def: &mut FunDecl) {
    if def.signature.output.is_unit() {
        transform_body(fmt_ctx, &def.name, &mut def.body);
    }
}
fn transform_global<'ctx>(fmt_ctx: &CtxNames<'ctx>, def: &mut GlobalDecl) {
    if def.ty.is_unit() {
        transform_body(fmt_ctx, &def.name, &mut def.body);
    }
}

pub fn transform<'ctx>(fmt_ctx: &CtxNames<'ctx>, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    funs.iter_mut().for_each(|d| transform_function(fmt_ctx, d));
    globals
        .iter_mut()
        .for_each(|d| transform_global(fmt_ctx, d));
}
