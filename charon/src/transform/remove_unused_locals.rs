//! Remove the locals (which are not used for the input arguments) which are
//! never used in the function bodies.  This is useful to remove the locals with
//! type `Never`. We actually check that there are no such local variables
//! remaining afterwards.
use crate::ids::Vector;
use crate::llbc_ast::{ExprBody, Statement};
use crate::transform::TransformCtx;
use crate::ullbc_ast::Var;
use crate::values::*;
use derive_visitor::{visitor_enter_fn, visitor_enter_fn_mut, Drive, DriveMut};
use std::collections::{HashMap, HashSet};
use take_mut::take;

use super::ctx::LlbcPass;

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
    let mut used_locals_cnt: HashMap<VarId, _> = HashMap::default();
    st.drive(&mut visitor_enter_fn(|vid: &VarId| {
        match used_locals_cnt.get_mut(vid) {
            None => {
                let _ = used_locals_cnt.insert(*vid, 1);
            }
            Some(cnt) => *cnt += 1,
        }
    }));
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

    (locals, vids_map)
}

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        take(b, |mut b| {
            let (locals, vids_map) = update_locals(b.arg_count, b.locals, &b.body);
            b.locals = locals;
            trace!("vids_maps: {:?}", vids_map);

            // Update all `VarId`s.
            b.body
                .drive_mut(&mut visitor_enter_fn_mut(|vid: &mut VarId| {
                    *vid = *vids_map.get(vid).unwrap();
                }));
            b
        });
    }
}
