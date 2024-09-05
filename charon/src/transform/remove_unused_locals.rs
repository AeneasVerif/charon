//! Remove the locals (which are not used for the input arguments) which are
//! never used in the function bodies.  This is useful to remove the locals with
//! type `Never`. We actually check that there are no such local variables
//! remaining afterwards.
use crate::llbc_ast::ExprBody;
use crate::transform::TransformCtx;
use crate::ullbc_ast::Var;
use crate::values::*;
use derive_visitor::{visitor_enter_fn, visitor_enter_fn_mut, Drive, DriveMut};
use std::collections::{HashMap, HashSet};
use std::mem;

use super::ctx::LlbcPass;

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        // Compute the set of used locals.
        // We always register the return variable and the input arguments.
        let mut used_locals: HashSet<VarId> =
            (0..(b.arg_count + 1)).map(|i| VarId::new(i)).collect();
        b.body.drive(&mut visitor_enter_fn(|vid: &VarId| {
            used_locals.insert(*vid);
        }));
        trace!("used_locals: {:?}", used_locals);

        // Keep only the variables that are used and update their indices to be contiguous.
        let mut vids_map: HashMap<VarId, VarId> = HashMap::new();
        for var in mem::take(&mut b.locals) {
            if used_locals.contains(&var.index) {
                let old_id = var.index;
                let new_id = b.locals.push_with(|index| Var { index, ..var });
                vids_map.insert(old_id, new_id);
            }
        }
        trace!("vids_maps: {:?}", vids_map);

        // Update all `VarId`s.
        b.body
            .drive_mut(&mut visitor_enter_fn_mut(|vid: &mut VarId| {
                *vid = *vids_map.get(vid).unwrap();
            }));
    }
}
