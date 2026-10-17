//! Reconstruct places that rustc split with `CopyForDeref` in elaborated MIR.
//!
//! A statement like `*tuple.1 = x` can become `_tmp = noretag copy tuple.1; *_tmp = x`.
//! The copy only reads the pointer; we put the dereference back on `tuple.1`. This also
//! applies to shared references and boxes, and to reads of pointer metadata.
use std::ops::ControlFlow;

use crate::ids::IndexVec;
use crate::transform::TransformCtx;
use crate::transform::ctx::UllbcPass;
use crate::ullbc_ast::*;

#[derive(Default)]
struct CopyInfo {
    assignment: Option<(StmtLoc, Place)>,
    use_loc: Option<StmtLoc>,
    /// Whether this local is used in any way that doesn't allow the merging we want.
    invalid: bool,
}

#[derive(Visitor)]
struct UseCollector<'a> {
    body: &'a ExprBody,
    copies: &'a mut IndexVec<LocalId, CopyInfo>,
    has_candidate: bool,
    current_st: Option<StmtLoc>,
}

impl VisitBody for UseCollector<'_> {
    fn visit_place(&mut self, place: &Place) -> ControlFlow<Self::Break> {
        if let Some((subplace, ProjectionElem::Deref | ProjectionElem::PtrMetadata)) =
            place.as_projection()
            && let Some(local) = subplace.as_local()
        {
            let info = &mut self.copies[local];
            if let Some(loc) = self.current_st
                && (info.use_loc.is_none() || info.use_loc == self.current_st)
            {
                info.use_loc = self.current_st;
                // We conservatively skip replacing into a statement that has by-move operands, to
                // avoid cases like:
                //   tmp = noretag copy pair._0
                //   out = (move pair._0, copy (*tmp))
                self.body[loc].dyn_visit_in_body(|operand: &Operand| {
                    info.invalid |= matches!(operand, Operand::Move(_));
                });
            } else {
                info.invalid = true;
            }
            // Don't visit the local.
            return ControlFlow::Continue(());
        }

        if let Some(local) = place.as_local() {
            // If we get to here then this is an invalid use.
            self.copies[local].invalid = true;
        }
        self.visit_inner(place)
    }

    fn visit_ullbc_statement(&mut self, st: &Statement) -> ControlFlow<Self::Break> {
        if let StatementKind::Assign(dest, rvalue) = &st.kind
            && let Some(local) = dest.as_local()
            && let Some(loc) = self.current_st
        {
            let info = &mut self.copies[local];
            if info.assignment.is_some() {
                info.invalid = true;
            } else if let Rvalue::Use(Operand::Copy(source), WithRetag::No) = rvalue
                && (matches!(source.ty().kind(), TyKind::Ref(..)) || source.ty().is_box())
                && !info.invalid
            {
                info.assignment = Some((loc, source.clone()));
                self.has_candidate = true;
            } else {
                info.invalid = true;
            }
            self.visit(rvalue)
        } else {
            self.visit_inner(st)
        }
    }
}

pub struct Transform;

impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut ExprBody) {
        let mut copies: IndexVec<LocalId, CopyInfo> =
            body.locals.locals.map_ref(|_| CopyInfo::default());

        // Look for locals that are assigned exactly once with a non-retagging copy. A local is
        // eligible only if every use is beneath a dereference or a metadata projection.
        let mut collector = UseCollector {
            body,
            copies: &mut copies,
            has_candidate: false,
            current_st: None,
        };
        for (block, data) in body.body.iter_enumerated() {
            for (statement, st) in data.statements.iter().enumerate() {
                collector.current_st = Some(StmtLoc::new(block, statement));
                collector.visit(st);
            }
            collector.current_st = None;
            collector.visit(&data.terminator);
        }
        if !collector.has_candidate {
            return;
        }

        // Inlining the source is safe only if nothing can change it between the
        // pointer read and its use. Nops do not affect that ordering.
        let uninterrupted = |body: &ExprBody, before: StmtLoc, after: StmtLoc| {
            before.block == after.block
                && before.statement < after.statement
                && body.body[before.block].statements[before.statement + 1..after.statement]
                    .iter()
                    .all(|st| st.kind.is_nop())
        };
        let mut replacements: IndexMap<LocalId, Place> = IndexMap::new();
        for (local, info) in copies.iter_enumerated() {
            if !info.invalid
                && let Some((assignment, source)) = &info.assignment
                && let Some(use_loc) = info.use_loc
                && uninterrupted(body, *assignment, use_loc)
            {
                replacements.insert(local, source.clone());
                body[*assignment].kind = StatementKind::Nop;
            }
        }
        if replacements.is_empty() {
            return;
        }

        body.body.dyn_visit_in_body_mut(|place: &mut Place| {
            // Keep the projection and replace only its base; the visitor reaches
            // inner projections on its own.
            if let PlaceKind::Projection(
                subplace,
                ProjectionElem::Deref | ProjectionElem::PtrMetadata,
            ) = &mut place.kind
                && let Some(local) = subplace.as_local()
                && let Some(source) = replacements.get(local)
            {
                **subplace = source.clone();
            }
        });
    }
}
