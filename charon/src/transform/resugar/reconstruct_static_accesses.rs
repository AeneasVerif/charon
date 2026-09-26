//! MIR places can't name statics, so rustc accesses a static through a temporary holding its
//! address, e.g. `_1 = const {alloc}; _0 = copy (*_1)` where the constant points to the static.
//! We turn `*_1` back into the static itself and remove the temporary.
//! This is needed to reliably tell what static accesses are unsafe (see `HasSafety`), as rustc
//! will lower safe static access to otherwise unsafe raw pointer accesses.
use rustc_hash::FxHashMap as HashMap;

use crate::transform::TransformCtx;
use crate::transform::ctx::UllbcPass;
use crate::ullbc_ast::*;

/// A local assigned the address of a static.
struct StaticInfo {
    global: GlobalDeclRef,
    assign_loc: StmtLoc,
    uses: usize,
    derefs: usize,
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, ctx: &mut TransformCtx, body: &mut ExprBody) {
        // Find the locals assigned the address of a static, and where they're assigned.
        let mut statics: HashMap<LocalId, StaticInfo> = body
            .body
            .iter_enumerated()
            .flat_map(|(block_id, block)| {
                let locs = (0..).map(move |i| StmtLoc::new(block_id, i));
                locs.zip(&block.statements)
            })
            .filter_map(|(loc, st)| {
                let (dest, rvalue) = &st.kind.as_assign()?;
                let global = match rvalue {
                    // `Ref` for non-mut statics, `Ptr` for `static mut` and extern statics
                    Rvalue::Use(Operand::Const(c), _)
                        if let ConstantExprKind::Ref(pointee, _)
                        | ConstantExprKind::Ptr(_, pointee, _) = c.kind() =>
                    {
                        pointee.kind().as_global()?
                    }
                    // Thread-local statics are accessed through `Rvalue::ThreadLocalRef` in MIR.
                    Rvalue::Ref { place, .. } | Rvalue::RawPtr { place, .. } => {
                        place.kind.as_global()?
                    }
                    _ => return None,
                };
                let decl = ctx.translated.global_decls.get(global.id)?;
                if !matches!(decl.global_kind, GlobalKind::Static { .. }) {
                    return None;
                }
                let info = StaticInfo {
                    global: global.clone(),
                    assign_loc: loc,
                    uses: 0,
                    derefs: 0,
                };
                Some((dest.as_local()?, info))
            })
            .collect();
        if statics.is_empty() {
            return;
        }

        // All desugared uses of a static go through its address, i.e. all its uses
        // are `*_static_addr` except when it is assigned to.
        body.body.dyn_visit_in_body(|place: &Place| {
            if let Some(local) = place.as_local()
                && let Some(info) = statics.get_mut(&local)
            {
                info.uses += 1;
            } else if let Some((sub, ProjectionElem::Deref)) = place.as_projection()
                && let Some(local) = sub.as_local()
                && let Some(info) = statics.get_mut(&local)
            {
                info.derefs += 1;
            }
        });
        statics.retain(|_, info| info.uses == info.derefs + 1);
        if statics.is_empty() {
            return;
        }

        // Remove the initial assignment (`_static_addr = const {alloc}`)
        for info in statics.values() {
            body[info.assign_loc].kind = StatementKind::Nop;
        }
        // ...and replace all derefs of the local with the static itself.
        body.body.dyn_visit_in_body_mut(|place: &mut Place| {
            if let Some((sub, ProjectionElem::Deref)) = place.as_projection()
                && let Some(local) = sub.as_local()
                && let Some(info) = statics.get(&local)
            {
                *place = Place::new_global(info.global.clone(), place.ty.clone());
            }
        });
    }
}
