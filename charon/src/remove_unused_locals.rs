//! Remove the locals (which are not used for the input arguments) which are
//! never used in the function bodies.  This is useful to remove the locals with
//! type `Never`. We actually check that there are no such local variables
//! remaining afterwards.

use crate::expressions::MutExprVisitor;
use crate::id_vector::ToUsize;
use crate::llbc_ast::{CtxNames, FunDecls, GlobalDecls, MutAstVisitor, Statement};
use crate::ullbc_ast::{iter_function_bodies, iter_global_bodies, Var};
use crate::values::*;
use std::collections::{HashMap, HashSet};
use take_mut::take;

#[derive(Debug, Clone)]
struct UpdateUsedLocals {
    vids_map: HashMap<VarId::Id, VarId::Id>,
}

impl UpdateUsedLocals {
    fn update_statement(vids_map: HashMap<VarId::Id, VarId::Id>, st: &mut Statement) {
        let mut v = UpdateUsedLocals { vids_map };
        v.visit_statement(st);
    }
}

impl MutExprVisitor for UpdateUsedLocals {
    fn visit_var_id(&mut self, vid: &mut VarId::Id) {
        *vid = *self.vids_map.get(vid).unwrap();
    }
}

impl MutAstVisitor for UpdateUsedLocals {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}
}

/// Compute the set of used locals, filter the unused locals and compute a new
/// mapping from variable index to variable index.
fn update_locals(
    num_inputs: usize,
    old_locals: VarId::Vector<Var>,
    st: &Statement,
) -> (VarId::Vector<Var>, HashMap<VarId::Id, VarId::Id>) {
    // Compute the set of used locals
    let mut used_locals: HashSet<VarId::Id> = HashSet::new();
    // We always register the return variable and the input arguments
    for i in 0..(num_inputs + 1) {
        used_locals.insert(VarId::Id::new(i));
    }
    // Explore the body
    let used_locals_cnt = crate::simplify_ops::ComputeUsedLocals::compute_in_statement(st);
    for (vid, cnt) in used_locals_cnt.iter() {
        if *cnt > 0 {
            used_locals.insert(*vid);
        }
    }
    trace!("used_locals_cnt: {:?}", used_locals_cnt);

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

pub fn transform(fmt_ctx: &CtxNames<'_>, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to remove unused locals in decl: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
        take(b, |mut b| {
            let (locals, vids_map) = update_locals(b.arg_count, b.locals, &b.body);
            b.locals = locals;
            trace!("vids_maps: {:?}", vids_map);
            UpdateUsedLocals::update_statement(vids_map, &mut b.body);
            b
        });
        trace!(
            "# After removing locals of: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
    }
}
