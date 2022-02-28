//! When the function's return type is unit, the generated MIR doesn't
//! set the return value to `()`. This can be a concern: in the case
//! of AENEAS, it means the return variable contains ⊥ upon returning.
//! For this reason, when the function has return type unit, we insert
//! an extra assignment just before returning.
use crate::cfim_ast::*;
use crate::expressions::*;
use crate::values::*;
use std::iter::FromIterator;

fn transform_st(st: Statement) -> Statement {
    match st {
        Statement::Return => {
            // The interesting case
            let ret_place = Place {
                var_id: VarId::Id::new(0),
                projection: Projection::new(),
            };
            let unit_value = Rvalue::Aggregate(AggregateKind::Tuple, Vec::new());
            let assign_st = Statement::Assign(ret_place, unit_value);
            let ret_st = Statement::Return;
            Statement::Sequence(Box::new(assign_st), Box::new(ret_st))
        }
        Statement::Assign(p, rv) => Statement::Assign(p, rv),
        Statement::FakeRead(p) => Statement::FakeRead(p),
        Statement::SetDiscriminant(p, vid) => Statement::SetDiscriminant(p, vid),
        Statement::Drop(p) => Statement::Drop(p),
        Statement::Assert(assert) => Statement::Assert(assert),
        Statement::Call(call) => Statement::Call(call),
        Statement::Panic => Statement::Panic,
        Statement::Break(i) => Statement::Break(i),
        Statement::Continue(i) => Statement::Continue(i),
        Statement::Nop => Statement::Nop,
        Statement::Switch(op, targets) => match targets {
            SwitchTargets::If(st1, st2) => {
                let st1 = Box::new(transform_st(*st1));
                let st2 = Box::new(transform_st(*st2));
                Statement::Switch(op, SwitchTargets::If(st1, st2))
            }
            SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                let targets =
                    Vec::from_iter(targets.into_iter().map(|(v, e)| (v, transform_st(e))));
                let otherwise = transform_st(*otherwise);
                let targets = SwitchTargets::SwitchInt(int_ty, targets, Box::new(otherwise));
                Statement::Switch(op, targets)
            }
        },
        Statement::Loop(loop_body) => Statement::Loop(Box::new(transform_st(*loop_body))),
        Statement::Sequence(st1, st2) => {
            Statement::Sequence(Box::new(transform_st(*st1)), Box::new(transform_st(*st2)))
        }
    }
}
fn transform_def(mut def: FunDecl) -> FunDecl {
    trace!("About to update: {}", def.name);
    // If the return type is unit: apply the transformation
    if def.signature.output.is_unit() {
        def.body = transform_st(def.body);
        def
    }
    // Otherwise, do nothing
    else {
        def
    }
}

pub fn transform(defs: FunDecls) -> FunDecls {
    FunDecls::from_iter(defs.into_iter().map(|def| transform_def(def)))
}
