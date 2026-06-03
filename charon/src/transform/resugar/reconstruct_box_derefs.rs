//! Resugar the box derefs that got desugared in elaborated MIR.
//!
//! In elaborated MIR, box derefs become actual accesses to the contained raw pointer. Under
//! `--treat-box-as-builtin`, we convert these back to derefs on the box.
use std::ops::ControlFlow;

use derive_generic_visitor::*;

use crate::ast::ullbc_ast_utils::StmtLoc;
use crate::ast::*;
use crate::ids::IndexVec;
use crate::transform::TransformCtx;
use crate::transform::ctx::UllbcPass;
use crate::ullbc_ast::{ExprBody, StatementKind};

pub struct Transform;

/// Look for
/// ```ignore
/// transmute::<NonNull<T>, *const T>(copy (*b).0)
/// ```
/// Returns `*b`
fn box_pointee_pointer_assignment(rvalue: &Rvalue) -> Option<Place> {
    let Rvalue::UnaryOp(
        UnOp::Cast(CastKind::Transmute(_, raw_ptr_ty)),
        Operand::Copy(hidden_pointer),
    ) = &rvalue
    else {
        return None;
    };
    let (field_base, ProjectionElem::Field(_, FieldId::ZERO)) = hidden_pointer.as_projection()?
    else {
        return None;
    };
    let (box_place, ProjectionElem::Deref) = field_base.as_projection()? else {
        return None;
    };
    let TyKind::Adt(TypeDeclRef {
        id: TypeId::Builtin(BuiltinTy::Box),
        generics: box_generics,
    }) = box_place.ty().kind()
    else {
        return None;
    };
    if &box_generics.types[0] != raw_ptr_ty.as_raw_ptr()?.0 {
        return None;
    }
    Some(box_place.clone().deref())
}

#[derive(Default)]
struct LocalStatus {
    /// Whether that local is the target of the special `transmute` statement we're looking for.
    /// Stores the `*b` where `b` is the Box.
    box_pointee_assignment: Option<(StmtLoc, Place)>,
    /// Whether that local is the target of more than one such special `transmute`.
    ambiguous: bool,
    /// Whether that local is ever used outside of a deref projection (apart from the initial
    /// assignment).
    used_outside_derefs: bool,
}

impl LocalStatus {
    fn rewritable_box_pointee(&self) -> Option<&(StmtLoc, Place)> {
        if self.ambiguous || self.used_outside_derefs {
            return None;
        }
        self.box_pointee_assignment.as_ref()
    }
}

struct LocalStatusCollector {
    local_status: IndexVec<LocalId, LocalStatus>,
    current_statement: Option<StmtLoc>,
}

impl Visitor for LocalStatusCollector {
    type Break = std::convert::Infallible;
}

impl VisitBody for LocalStatusCollector {
    fn visit_place(&mut self, place: &Place) -> ControlFlow<Self::Break> {
        match &place.kind {
            // Skip uses of a local where the last projection is a deref.
            PlaceKind::Projection(subplace, pj) if subplace.is_local() && pj.is_deref() => {
                return ControlFlow::Continue(());
            }
            // This didn't get caught by the branch above, so it's an invalid use.
            PlaceKind::Local(local) => self.local_status[*local].used_outside_derefs = true,
            _ => {}
        }
        self.visit_inner(place)
    }

    fn visit_ullbc_statement(&mut self, st: &ullbc_ast::Statement) -> ControlFlow<Self::Break> {
        if let StatementKind::Assign(dst, rvalue) = &st.kind
            && let Some(local) = dst.as_local()
            && let Some(box_pointee) = box_pointee_pointer_assignment(rvalue)
        {
            let status = &mut self.local_status[local];
            if status.box_pointee_assignment.is_some() {
                status.ambiguous = true;
            } else {
                let loc = self.current_statement.unwrap();
                status.box_pointee_assignment = Some((loc, box_pointee));
            }
            // Ignore the assignment destination: this initialization is the one non-deref
            // interaction allowed for the temporary pointer.
            self.visit(rvalue)
        } else {
            self.visit_inner(st)
        }
    }
}

fn collect_local_status(body: &ExprBody) -> IndexVec<LocalId, LocalStatus> {
    let mut collector = LocalStatusCollector {
        local_status: body.locals.locals.map_ref(|_| Default::default()),
        current_statement: None,
    };
    for (block, block_data) in body.body.iter_enumerated() {
        for (statement, st) in block_data.statements.iter().enumerate() {
            collector.current_statement = Some(StmtLoc::new(block, statement));
            let _ = collector.visit(st);
        }
        collector.current_statement = None;
        let _ = collector.visit(&block_data.terminator);
    }
    collector.local_status
}

fn rewrite_place(place: &mut Place, local_status: &IndexVec<LocalId, LocalStatus>) {
    let Some((subplace, projection)) = place.as_projection() else {
        return;
    };
    if projection == &ProjectionElem::Deref
        && let Some(local) = subplace.as_local()
        && let Some((_, box_pointee)) = local_status[local].rewritable_box_pointee()
    {
        *place = box_pointee.clone();
        return;
    }

    let PlaceKind::Projection(subplace, _) = &mut place.kind else {
        unreachable!();
    };
    rewrite_place(subplace, local_status);
}

impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.treat_box_as_builtin
    }

    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut ExprBody) {
        let local_status = collect_local_status(body);

        body.body.dyn_visit_in_body_mut(|place: &mut Place| {
            rewrite_place(place, &local_status);
        });

        for status in local_status {
            if let Some((assign_loc, _)) = status.rewritable_box_pointee() {
                body[*assign_loc].kind = StatementKind::Nop;
            }
        }
    }
}
