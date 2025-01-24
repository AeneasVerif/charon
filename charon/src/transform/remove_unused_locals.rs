//! Remove the locals (which are not used for the input arguments) which are
//! never used in the function bodies.  This is useful to remove the locals with
//! type `Never`. We actually check that there are no such local variables
//! remaining afterwards.
use std::collections::{HashMap, HashSet};
use std::mem;

use crate::ast::*;
use crate::transform::TransformCtx;

use super::ctx::TransformPass;

fn remove_unused_locals<Body: BodyVisitable>(body: &mut GExprBody<Body>) {
    // Compute the set of used locals.
    // We always register the return variable and the input arguments.
    let mut used_locals: HashSet<VarId> = (0..(body.locals.arg_count + 1))
        .map(|i| VarId::new(i))
        .collect();
    body.body.dyn_visit_in_body(|vid: &VarId| {
        used_locals.insert(*vid);
    });
    trace!("used_locals: {:?}", used_locals);

    // Keep only the variables that are used and update their indices to be contiguous.
    let mut vids_map: HashMap<VarId, VarId> = HashMap::new();
    for var in mem::take(&mut body.locals.vars) {
        if used_locals.contains(&var.index) {
            let old_id = var.index;
            let new_id = body.locals.vars.push_with(|index| Var { index, ..var });
            vids_map.insert(old_id, new_id);
        }
    }
    trace!("vids_maps: {:?}", vids_map);

    // Update all `VarId`s.
    body.body.dyn_visit_in_body_mut(|vid: &mut VarId| {
        *vid = *vids_map.get(vid).unwrap();
    });
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        ctx.for_each_fun_decl(|_ctx, fun| {
            if let Ok(body) = &mut fun.body {
                match body {
                    Body::Unstructured(body) => remove_unused_locals(body),
                    Body::Structured(body) => remove_unused_locals(body),
                }
            }
        });
    }
}
