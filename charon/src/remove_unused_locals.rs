use take_mut::take;

/// Remove the locals which are never used in the function bodies.
/// This is useful to remove the locals with type `Never`. We actually
/// check that there are no such local variables remaining afterwards.
use crate::expressions::*;
use crate::id_vector::ToUsize;
use crate::llbc_ast::{CtxNames, FunDecls, GlobalDecls, RawStatement, Statement, SwitchTargets};
use crate::ullbc_ast::{iter_function_bodies, iter_global_bodies, Var};
use crate::values::*;
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

fn compute_used_locals_in_place(locals: &mut HashSet<VarId::Id>, p: &Place) {
    locals.insert(p.var_id);
}

fn compute_used_locals_in_operand(locals: &mut HashSet<VarId::Id>, op: &Operand) {
    match op {
        Operand::Copy(p) | Operand::Move(p) => compute_used_locals_in_place(locals, p),
        Operand::Const(_, _) => (),
    }
}

fn compute_used_locals_in_operands(locals: &mut HashSet<VarId::Id>, ops: &Vec<Operand>) {
    for op in ops {
        compute_used_locals_in_operand(locals, op)
    }
}

fn compute_used_locals_in_rvalue(locals: &mut HashSet<VarId::Id>, rv: &Rvalue) {
    match rv {
        Rvalue::Use(op) => compute_used_locals_in_operand(locals, op),
        Rvalue::Ref(p, _) => compute_used_locals_in_place(locals, p),
        Rvalue::UnaryOp(_, op) => compute_used_locals_in_operand(locals, op),
        Rvalue::BinaryOp(_, op1, op2) => {
            compute_used_locals_in_operand(locals, op1);
            compute_used_locals_in_operand(locals, op2);
        }
        Rvalue::Discriminant(p) => compute_used_locals_in_place(locals, p),
        Rvalue::Aggregate(_, ops) => {
            compute_used_locals_in_operands(locals, ops);
        }
    }
}

fn compute_used_locals_in_statement(locals: &mut HashSet<VarId::Id>, st: &Statement) {
    match &st.content {
        RawStatement::Return => (),
        RawStatement::Assign(p, rv) => {
            compute_used_locals_in_rvalue(locals, rv);
            compute_used_locals_in_place(locals, p);
        }
        RawStatement::AssignGlobal(id, _) => {
            locals.insert(*id);
        }
        RawStatement::FakeRead(p) => compute_used_locals_in_place(locals, p),
        RawStatement::SetDiscriminant(p, _) => compute_used_locals_in_place(locals, p),
        RawStatement::Drop(p) => compute_used_locals_in_place(locals, p),
        RawStatement::Assert(assert) => compute_used_locals_in_operand(locals, &assert.cond),
        RawStatement::Call(call) => {
            compute_used_locals_in_operands(locals, &call.args);
            compute_used_locals_in_place(locals, &call.dest);
        }
        RawStatement::Panic => (),
        RawStatement::Break(_) => (),
        RawStatement::Continue(_) => (),
        RawStatement::Nop => (),
        RawStatement::Switch(op, targets) => {
            compute_used_locals_in_operand(locals, op);
            match targets {
                SwitchTargets::If(st1, st2) => {
                    compute_used_locals_in_statement(locals, st1);
                    compute_used_locals_in_statement(locals, st2);
                }
                SwitchTargets::SwitchInt(_, targets, otherwise) => {
                    compute_used_locals_in_statement(locals, otherwise);
                    for (_, tgt) in targets {
                        compute_used_locals_in_statement(locals, tgt);
                    }
                }
            }
        }
        RawStatement::Loop(loop_body) => compute_used_locals_in_statement(locals, loop_body),
        RawStatement::Sequence(st1, st2) => {
            compute_used_locals_in_statement(locals, st1);
            compute_used_locals_in_statement(locals, st2);
        }
    }
}

fn transform_place(vids_map: &HashMap<VarId::Id, VarId::Id>, mut p: Place) -> Place {
    let nvid = vids_map.get(&p.var_id).unwrap();
    p.var_id = *nvid;
    p
}

fn transform_operand(vids_map: &HashMap<VarId::Id, VarId::Id>, op: Operand) -> Operand {
    match op {
        Operand::Copy(p) => Operand::Copy(transform_place(vids_map, p)),
        Operand::Move(p) => Operand::Move(transform_place(vids_map, p)),
        Operand::Const(ty, cv) => Operand::Const(ty, cv),
    }
}

fn transform_operands(vids_map: &HashMap<VarId::Id, VarId::Id>, ops: Vec<Operand>) -> Vec<Operand> {
    ops.into_iter()
        .map(|op| transform_operand(vids_map, op))
        .collect()
}

fn transform_rvalue(vids_map: &HashMap<VarId::Id, VarId::Id>, rv: Rvalue) -> Rvalue {
    match rv {
        Rvalue::Use(op) => Rvalue::Use(transform_operand(vids_map, op)),
        Rvalue::Ref(p, kind) => Rvalue::Ref(transform_place(vids_map, p), kind),
        Rvalue::UnaryOp(unop, op) => Rvalue::UnaryOp(unop, transform_operand(vids_map, op)),
        Rvalue::BinaryOp(binop, op1, op2) => {
            let op1 = transform_operand(vids_map, op1);
            let op2 = transform_operand(vids_map, op2);
            Rvalue::BinaryOp(binop, op1, op2)
        }
        Rvalue::Discriminant(p) => Rvalue::Discriminant(transform_place(vids_map, p)),
        Rvalue::Aggregate(kind, ops) => {
            let ops = transform_operands(vids_map, ops);
            Rvalue::Aggregate(kind, ops)
        }
    }
}

fn transform_st(vids_map: &HashMap<VarId::Id, VarId::Id>, st: Statement) -> Statement {
    let st_raw = match st.content {
        RawStatement::Return => RawStatement::Return,
        RawStatement::Assign(p, rv) => {
            RawStatement::Assign(transform_place(vids_map, p), transform_rvalue(vids_map, rv))
        }
        RawStatement::AssignGlobal(id, gid) => {
            RawStatement::AssignGlobal(*vids_map.get(&id).unwrap(), gid)
        }
        RawStatement::FakeRead(p) => RawStatement::FakeRead(transform_place(vids_map, p)),
        RawStatement::SetDiscriminant(p, variant_id) => {
            RawStatement::SetDiscriminant(transform_place(vids_map, p), variant_id)
        }
        RawStatement::Drop(p) => RawStatement::Drop(transform_place(vids_map, p)),
        RawStatement::Assert(mut assert) => {
            assert.cond = transform_operand(vids_map, assert.cond);
            RawStatement::Assert(assert)
        }
        RawStatement::Call(mut call) => {
            call.args = transform_operands(vids_map, call.args);
            call.dest = transform_place(vids_map, call.dest);
            RawStatement::Call(call)
        }
        RawStatement::Panic => RawStatement::Panic,
        RawStatement::Break(i) => RawStatement::Break(i),
        RawStatement::Continue(i) => RawStatement::Continue(i),
        RawStatement::Nop => RawStatement::Nop,
        RawStatement::Switch(op, targets) => {
            let op = transform_operand(vids_map, op);
            match targets {
                SwitchTargets::If(st1, st2) => {
                    let st1 = Box::new(transform_st(vids_map, *st1));
                    let st2 = Box::new(transform_st(vids_map, *st2));
                    RawStatement::Switch(op, SwitchTargets::If(st1, st2))
                }
                SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                    let targets = Vec::from_iter(
                        targets
                            .into_iter()
                            .map(|(v, e)| (v, transform_st(vids_map, e))),
                    );
                    let otherwise = transform_st(vids_map, *otherwise);
                    let targets = SwitchTargets::SwitchInt(int_ty, targets, Box::new(otherwise));
                    RawStatement::Switch(op, targets)
                }
            }
        }
        RawStatement::Loop(loop_body) => {
            RawStatement::Loop(Box::new(transform_st(vids_map, *loop_body)))
        }
        RawStatement::Sequence(st1, st2) => RawStatement::Sequence(
            Box::new(transform_st(vids_map, *st1)),
            Box::new(transform_st(vids_map, *st2)),
        ),
    };

    Statement::new(st.meta, st_raw)
}

fn update_locals(
    old_locals: VarId::Vector<Var>,
    st: &Statement,
) -> (VarId::Vector<Var>, HashMap<VarId::Id, VarId::Id>) {
    // Compute the set of used locals
    let mut used_locals: HashSet<VarId::Id> = HashSet::new();
    // We always register the return variable
    used_locals.insert(VarId::Id::new(0));
    // Explore the body
    compute_used_locals_in_statement(&mut used_locals, st);

    // Filter: only keep the variables which are used, and update
    // their indices so as not to have "holes"
    let mut vids_map: HashMap<VarId::Id, VarId::Id> = HashMap::new();
    let mut locals: VarId::Vector<Var> = VarId::Vector::new();
    let mut var_id_counter = VarId::Generator::new();
    for mut var in old_locals {
        if used_locals.contains(&var.index) {
            let old_id = var.index;
            let new_id = var_id_counter.fresh_id();
            var.index = new_id;
            vids_map.insert(old_id, new_id);
            assert!(new_id.to_usize() == locals.len());
            locals.push_back(var);
        }
    }

    // Check there are no remaining variables with type `Never`
    for v in &locals {
        assert!(!v.ty.contains_never());
    }
    (locals, vids_map)
}

pub fn transform<'ctx>(fmt_ctx: &CtxNames<'ctx>, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to remove unused locals in decl: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
        take(b, |mut b| {
            let (locals, vids_map) = update_locals(b.locals, &b.body);
            b.locals = locals;
            b.body = transform_st(&vids_map, b.body);
            b
        });
    }
}
