//! Remove the locals (which are not used for the input arguments) which are
//! never used in the function bodies.  This is useful to remove the locals with
//! type `Never`. We actually check that there are no such local variables
//! remaining afterwards.
use crate::expressions::{MutExprVisitor, SharedExprVisitor};
use crate::formatter::{Formatter, IntoFormatter};
use crate::ids::Vector;
use crate::llbc_ast::{MutAstVisitor, SharedAstVisitor, Statement};
use crate::translate_ctx::TransformCtx;
use crate::types::{MutTypeVisitor, SharedTypeVisitor};
use crate::ullbc_ast::Var;
use crate::values::*;
use std::collections::{HashMap, HashSet};
use take_mut::take;

#[derive(Debug, Clone)]
pub(crate) struct ComputeUsedLocals {
    vars: im::HashMap<VarId, usize>,
}

impl ComputeUsedLocals {
    fn new() -> Self {
        ComputeUsedLocals {
            vars: im::HashMap::new(),
        }
    }

    pub(crate) fn compute_in_statement(st: &Statement) -> im::HashMap<VarId, usize> {
        let mut visitor = Self::new();
        visitor.visit_statement(st);
        visitor.vars
    }
}

impl SharedTypeVisitor for ComputeUsedLocals {}
impl SharedExprVisitor for ComputeUsedLocals {
    fn visit_var_id(&mut self, vid: &VarId) {
        match self.vars.get_mut(vid) {
            Option::None => {
                let _ = self.vars.insert(*vid, 1);
            }
            Option::Some(cnt) => *cnt += 1,
        }
    }
}

impl SharedAstVisitor for ComputeUsedLocals {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        visitor(self)
    }

    fn merge(&mut self) {}
}

#[derive(Debug, Clone)]
struct UpdateUsedLocals {
    vids_map: HashMap<VarId, VarId>,
}

impl UpdateUsedLocals {
    fn update_statement(vids_map: HashMap<VarId, VarId>, st: &mut Statement) {
        let mut v = UpdateUsedLocals { vids_map };
        v.visit_statement(st);
    }
}

impl MutTypeVisitor for UpdateUsedLocals {}
impl MutExprVisitor for UpdateUsedLocals {
    fn visit_var_id(&mut self, vid: &mut VarId) {
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
    old_locals: Vector<VarId, Var>,
    st: &Statement,
) -> (Vector<VarId, Var>, HashMap<VarId, VarId>) {
    // Compute the set of used locals
    let mut used_locals: HashSet<VarId> = HashSet::new();
    // We always register the return variable and the input arguments
    for i in 0..(num_inputs + 1) {
        used_locals.insert(VarId::new(i));
    }
    // Explore the body
    let used_locals_cnt = ComputeUsedLocals::compute_in_statement(st);
    for (vid, cnt) in used_locals_cnt.iter() {
        if *cnt > 0 {
            used_locals.insert(*vid);
        }
    }
    trace!("used_locals_cnt: {:?}", used_locals_cnt);

    // Filter: only keep the variables which are used, and update
    // their indices so as not to have "holes"
    let mut vids_map: HashMap<VarId, VarId> = HashMap::new();
    let mut locals: Vector<VarId, Var> = Vector::new();
    for var in old_locals {
        if used_locals.contains(&var.index) {
            let old_id = var.index;
            let new_id = locals.push_with(|index| Var { index, ..var });
            vids_map.insert(old_id, new_id);
        }
    }

    // Check there are no remaining variables with type `Never`
    for v in &locals {
        assert!(!v.ty.contains_never());
    }
    (locals, vids_map)
}

pub fn transform(ctx: &mut TransformCtx) {
    ctx.iter_structured_bodies(|ctx, name, b| {
        let fmt_ctx = ctx.into_fmt();
        trace!(
            "# About to remove unused locals in decl: {}:\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );
        take(b, |mut b| {
            let (locals, vids_map) = update_locals(b.arg_count, b.locals, &b.body);
            b.locals = locals;
            trace!("vids_maps: {:?}", vids_map);
            UpdateUsedLocals::update_statement(vids_map, &mut b.body);
            b
        });
        let fmt_ctx = ctx.into_fmt();
        trace!(
            "# After removing unused locals of: {}:\n{}",
            name.fmt_with_ctx(&fmt_ctx),
            fmt_ctx.format_object(&*b)
        );
        // Check that there are no remaining locals with the type `Never`
        assert!(b.locals.iter().all(|v| !v.ty.is_never()));
    })
}
