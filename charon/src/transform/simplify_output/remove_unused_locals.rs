//! Remove the locals (which are not used for the input arguments) which are
//! never used in the function bodies.  This is useful to remove the locals with
//! type `Never`. We actually check that there are no such local variables
//! remaining afterwards.
use std::mem;

use crate::ast::*;
use crate::transform::TransformCtx;
use crate::transform::ctx::TransformPass;

fn remove_unused_locals<Body: BodyVisitable>(body: &mut GExprBody<Body>) {
    // Compute the set of used locals.
    // We always register the return variable and the input arguments.
    let mut used_locals: Vector<LocalId, bool> = body
        .locals
        .locals
        .map_ref(|local| local.index <= body.locals.arg_count);
    body.body.dyn_visit_in_body(|lid: &LocalId| {
        used_locals[*lid] = true;
    });
    trace!("used_locals: {:?}", used_locals);

    // Keep only the variables that are used and update their indices to be contiguous.
    let mut ids_map: Vector<LocalId, Option<LocalId>> = body.locals.locals.map_ref(|_| None);
    for local in mem::take(&mut body.locals.locals) {
        if used_locals[local.index] {
            let old_id = local.index;
            let new_id = body
                .locals
                .locals
                .push_with(|index| Local { index, ..local });
            ids_map[old_id] = Some(new_id);
        }
    }
    trace!("ids_maps: {:?}", ids_map);

    // Update all `LocalId`s.
    body.body.dyn_visit_in_body_mut(|lid: &mut LocalId| {
        *lid = ids_map[*lid].unwrap();
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
