use crate::formatter::IntoFormatter;
use crate::pretty::FmtWithCtx;
use crate::transform::TransformCtx;
use crate::transform::ctx::BodyTransformCtx;
use crate::transform::index_to_function_calls::compute_subslice_end_idx;
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

fn is_sized_type_var<T: BodyTransformCtx>(ctx: &mut T, ty: &Ty) -> bool {
    match ty.kind() {
        TyKind::TypeVar(..) => {
            if ctx.get_ctx().options.hide_marker_traits {
                // If we're hiding `Sized`, let's consider everything to be sized.
                return true;
            }
            let params = ctx.get_params();
            for clause in &params.trait_clauses {
                let tref = clause.trait_.clone().erase();
                // Check if it is `Sized<T>`
                if tref.generics.types[0] == *ty
                    && ctx
                        .get_ctx()
                        .translated
                        .trait_decls
                        .get(tref.id)
                        .and_then(|decl| decl.item_meta.lang_item.clone())
                        == Some("sized".into())
                {
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}

/// No metadata. We use the `unit_metadata` global to avoid having to define unit locals
/// everywhere.
fn no_metadata<T: BodyTransformCtx>(ctx: &T) -> Operand {
    let unit_meta = ctx.get_ctx().translated.unit_metadata.clone().unwrap();
    Operand::Copy(Place::new_global(unit_meta, Ty::mk_unit()))
}

/// Compute the metadata for a place. Return `None` if the place has no metadata.
fn compute_place_metadata_inner<T: BodyTransformCtx>(
    ctx: &mut T,
    place: &Place,
    metadata_ty: &Ty,
) -> Option<Operand> {
    let (subplace, proj) = place.as_projection()?;
    match proj {
        // The outermost deref we encountered gives us the metadata of the place.
        ProjectionElem::Deref => {
            let metadata_place = subplace
                .clone()
                .project(ProjectionElem::PtrMetadata, metadata_ty.clone());
            Some(Operand::Copy(metadata_place))
        }
        ProjectionElem::Field { .. } => compute_place_metadata_inner(ctx, subplace, metadata_ty),
        // Indexing for array & slice will only result in sized types, hence no metadata
        ProjectionElem::Index { .. } => None,
        // Ptr metadata is always sized.
        ProjectionElem::PtrMetadata { .. } => None,
        // Subslice must have metadata length, compute the metadata here as `to` - `from`
        ProjectionElem::Subslice { from, to, from_end } => {
            let to_idx = compute_subslice_end_idx(ctx, subplace, *to.clone(), *from_end);
            let diff_place = ctx.fresh_var(None, Ty::mk_usize());
            ctx.insert_assn_stmt(
                diff_place.clone(),
                // Overflow is UB and should have been prevented by a bound check beforehand.
                Rvalue::BinaryOp(BinOp::Sub(OverflowMode::UB), to_idx, *from.clone()),
            );
            Some(Operand::Copy(diff_place))
        }
    }
}

/// Emit statements that compute the metadata of the given place. Returns an operand containing the
/// metadata value.
pub fn compute_place_metadata<T: BodyTransformCtx>(ctx: &mut T, place: &Place) -> Operand {
    trace!(
        "getting ptr metadata for place: {}",
        place.with_ctx(&ctx.get_ctx().into_fmt())
    );
    let metadata_ty = place
        .ty()
        .get_ptr_metadata(&ctx.get_ctx().translated)
        .into_type();
    if metadata_ty.is_unit()
        || matches!(metadata_ty.kind(), TyKind::PtrMetadata(ty) if is_sized_type_var(ctx, ty))
    {
        // If the type var is known to be `Sized`, then no metadata is needed
        return no_metadata(ctx);
    }
    trace!(
        "computed metadata type: {}",
        metadata_ty.with_ctx(&ctx.get_ctx().into_fmt())
    );
    compute_place_metadata_inner(ctx, place, &metadata_ty).unwrap_or_else(|| no_metadata(ctx))
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
            *ptr_metadata = compute_place_metadata(self, place);
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
