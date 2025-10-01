use crate::transform::TransformCtx;
use crate::transform::ctx::BodyTransformCtx;
use crate::{transform::ctx::UllbcPass, ullbc_ast::*};
use derive_generic_visitor::*;

#[derive(Visitor)]
struct BodyVisitor<'a, 'b> {
    locals: &'a mut Locals,
    /// Statements to prepend to the statement currently being explored.
    statements: Vec<Statement>,
    span: Span,
    ctx: &'b TransformCtx,
    params: &'a GenericParams,
}

impl BodyTransformCtx for BodyVisitor<'_, '_> {
    fn get_ctx(&self) -> &TransformCtx {
        self.ctx
    }
    fn get_params(&self) -> &GenericParams {
        self.params
    }
    fn get_locals_mut(&mut self) -> &mut Locals {
        self.locals
    }

    fn insert_storage_live_stmt(&mut self, local: LocalId) {
        self.statements
            .push(Statement::new(self.span, StatementKind::StorageLive(local)));
    }

    fn insert_assn_stmt(&mut self, place: Place, rvalue: Rvalue) {
        self.statements.push(Statement::new(
            self.span,
            StatementKind::Assign(place, rvalue),
        ));
    }

    fn insert_storage_dead_stmt(&mut self, local: LocalId) {
        self.statements
            .push(Statement::new(self.span, StatementKind::StorageDead(local)));
    }
}

impl VisitBodyMut for BodyVisitor<'_, '_> {
    fn visit_rvalue(&mut self, x: &mut Rvalue) -> ::std::ops::ControlFlow<Self::Break> {
        if let Rvalue::Ref {
            place,
            ptr_metadata,
            ..
        }
        | Rvalue::RawPtr {
            place,
            ptr_metadata,
            ..
        } = x
        {
            *ptr_metadata = self.compute_place_metadata(place);
        }
        Continue(())
    }
}

pub struct Transform;

impl Transform {
    fn transform_body_with_param(
        &self,
        ctx: &mut TransformCtx,
        b: &mut ExprBody,
        params: &GenericParams,
    ) {
        b.body.iter_mut().for_each(|data| {
            data.transform(|st: &mut Statement| {
                let mut visitor = BodyVisitor {
                    locals: &mut b.locals,
                    statements: Vec::new(),
                    span: st.span,
                    ctx: &ctx,
                    params,
                };
                let _ = st.drive_body_mut(&mut visitor);
                visitor.statements
            });
        });
    }
}

/// This pass computes the metadata for Rvalue, which is used to create references and raw pointers.
/// E.g., in cases like:
/// ```ignore
/// let x = &[mut] (*some_v).field;
/// ```
/// If the `(*some_v).field` is a DST, like `[i32]`, we will need to fetch the metadata, i.e., the length of the slice,
/// and store it in a local variable, then we have:
/// ```ignore
/// let x = Rvalue::Ref { place:(*some_v).field, kind: [mut], ptr_metadata: PtrMetadata(some_v) };
/// ```
/// There should be a new local variable introduced to store `PtrMetadata(some_v)`.
impl UllbcPass for Transform {
    fn transform_function(&self, ctx: &mut TransformCtx, decl: &mut FunDecl) {
        if let Ok(body) = &mut decl.body {
            self.transform_body_with_param(
                ctx,
                body.as_unstructured_mut().unwrap(),
                &decl.signature.generics,
            )
        }
    }
}
