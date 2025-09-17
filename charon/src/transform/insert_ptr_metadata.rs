use crate::formatter::IntoFormatter;
use crate::pretty::FmtWithCtx;
use crate::transform::TransformCtx;
use crate::transform::ctx::BodyTransformCtx;
use crate::transform::index_to_function_calls::compute_to_idx;
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

fn is_last_field_of_ty_decl_id(
    ctx: &TransformCtx,
    type_decl_id: &TypeDeclId,
    field: &FieldId,
) -> bool {
    let type_decl = ctx.translated.type_decls.get(*type_decl_id).unwrap();
    match &type_decl.kind {
        TypeDeclKind::Struct(vector) => vector.slot_count() - 1 == field.index(),
        // `enum` does not have "last field" concept, also, it should not have metadata as per Rust rules
        TypeDeclKind::Enum(..) => false,
        // Same as `enum` above
        TypeDeclKind::Union(..) => false,
        TypeDeclKind::Opaque => panic!(
            "Accessing the field {} of an opaque type {}! Cannot tell whether this is the last field. Please consider translating the opaque type definition by `--include`.",
            field,
            type_decl_id.with_ctx(&ctx.into_fmt())
        ),
        TypeDeclKind::Alias(ty) => panic!(
            "Alias type {} should have been resolved before this point! Found alias to {}.",
            type_decl_id.with_ctx(&ctx.into_fmt()),
            ty.with_ctx(&ctx.into_fmt())
        ),
        TypeDeclKind::Error(_) => panic!("Accessing the field of an error type!"),
    }
}

fn is_last_field(ctx: &TransformCtx, proj_kind: &FieldProjKind, field: &FieldId) -> bool {
    match proj_kind {
        FieldProjKind::Adt(type_decl_id, _) => {
            is_last_field_of_ty_decl_id(ctx, type_decl_id, field)
        }
        FieldProjKind::Tuple(arity) => arity - 1 == field.index(),
    }
}

/// Get the outmost deref of a place, if it exists. Returns the place that the deref happens upon and the derefed type.
/// Also check if the projection always performs on the last field, otherwise return None,
/// as it should never have metadata if it is not the last field.
fn outmost_deref_at_last_field<T: BodyTransformCtx>(
    ctx: &mut T,
    place: &Place,
) -> Option<(Rvalue, Ty)> {
    let (subplace, proj) = place.as_projection()?;
    match proj {
        // *subplace
        // So that `subplace` is a pointer / reference type
        // We will need to keep the derefed type to get the metadata type
        ProjectionElem::Deref => Some((
            Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(subplace.clone())),
            place.ty().clone(),
        )),
        ProjectionElem::Field(proj_kind, field)
            if is_last_field(ctx.get_ctx(), proj_kind, field) =>
        {
            outmost_deref_at_last_field(ctx, subplace)
        }
        // This is not the last field, so it will never have metadata
        ProjectionElem::Field(..) => None,
        // Indexing for array & slice will only result in sized types, hence no metadata
        ProjectionElem::Index { .. } => None,
        // Subslice must have metadata length, compute the metadata here as `to` - `from`
        ProjectionElem::Subslice { from, to, from_end } => {
            let to_idx = compute_to_idx(ctx, subplace, *to.clone(), *from_end);
            let diff_place = ctx.fresh_var(None, Ty::mk_usize());
            ctx.insert_assn_stmt(
                diff_place.clone(),
                // `to` cannot be less than `from` as per Rust rules, so panic
                Rvalue::BinaryOp(BinOp::Sub(OverflowMode::UB), to_idx, *from.clone()),
            );
            Some((Rvalue::Use(Operand::Copy(diff_place)), place.ty().clone()))
        }
    }
}

fn is_sized_type_var<T: BodyTransformCtxWithParams>(ctx: &mut T, ty: &Ty) -> bool {
    match ty.kind() {
        TyKind::TypeVar(..) => {
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

fn get_ptr_metadata_aux<T: BodyTransformCtxWithParams>(
    ctx: &mut T,
    place: &Place,
) -> Option<Operand> {
    trace!(
        "getting ptr metadata for place: {}",
        place.with_ctx(&ctx.get_ctx().into_fmt())
    );
    let (rvalue, deref_ty) = outmost_deref_at_last_field(ctx, place)?;
    let ty = match deref_ty.get_ptr_metadata(&ctx.get_ctx().translated) {
        PtrMetadata::None => None,
        PtrMetadata::Length => Some(Ty::new(TyKind::Literal(LiteralTy::UInt(UIntTy::Usize)))),
        PtrMetadata::VTable(type_decl_ref) => Some(Ty::new(TyKind::Ref(
            Region::Static,
            Ty::new(TyKind::Adt(type_decl_ref)),
            RefKind::Shared,
        ))),
        // If the type var is known to be `Sized`, then no metadata is needed
        PtrMetadata::InheritFrom(ty) => {
            if is_sized_type_var(ctx, &ty) {
                None
            } else {
                Some(Ty::new(TyKind::PtrMetadata(ty)))
            }
        }
    }?;
    trace!(
        "computed metadata type: {}",
        ty.with_ctx(&ctx.get_ctx().into_fmt())
    );
    let new_place = ctx.fresh_var(None, ty);
    // it is `Copy` because `place` is a deref, which means it is a pointer / ref
    ctx.insert_assn_stmt(new_place.clone(), rvalue);
    Some(Operand::Move(new_place))
}

/// No metadata, use unit, but as const ADT (for `()`) is not allowed
/// Introduce a new local to hold this
fn no_metadata<T: BodyTransformCtx>(ctx: &mut T) -> Operand {
    let new_place = ctx.fresh_var(None, Ty::mk_unit());
    ctx.insert_assn_stmt(new_place.clone(), Rvalue::unit_value());
    Operand::Move(new_place)
}

/// When a place is to be referred to as a reference or a raw pointer, we compute the metadata required
/// for this operation and return it as an operand.
/// New locals & statements are to be inserted before the target place to keep the metadata.
pub fn place_ptr_metadata_operand<T: BodyTransformCtxWithParams>(
    ctx: &mut T,
    place: &Place,
) -> Operand {
    // add a shortcut here -- if the type is originally not a type with ptr-metadata, ignore it
    match place.ty().get_ptr_metadata(&ctx.get_ctx().translated) {
        PtrMetadata::None => return no_metadata(ctx),
        _ => match get_ptr_metadata_aux(ctx, place) {
            Some(metadata) => metadata,
            None => no_metadata(ctx),
        },
    }
}

pub trait BodyTransformCtxWithParams: BodyTransformCtx {
    fn get_params(&self) -> &GenericParams;
}

impl BodyTransformCtxWithParams for BodyVisitor<'_, '_> {
    fn get_params(&self) -> &GenericParams {
        self.params
    }
}

impl BodyTransformCtx for BodyVisitor<'_, '_> {
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

    fn get_ctx(&self) -> &TransformCtx {
        self.ctx
    }

    fn insert_storage_dead_stmt(&mut self, local: LocalId) {
        self.statements
            .push(Statement::new(self.span, StatementKind::StorageDead(local)));
    }
}

impl VisitBodyMut for BodyVisitor<'_, '_> {
    fn visit_rvalue(&mut self, x: &mut Rvalue) -> ::std::ops::ControlFlow<Self::Break> {
        match x {
            Rvalue::Ref { place, kind, .. } => {
                let metadata = place_ptr_metadata_operand(self, &place);
                *x = Rvalue::Ref {
                    place: place.clone(),
                    kind: *kind,
                    ptr_metadata: metadata,
                };
            }
            Rvalue::RawPtr { place, kind, .. } => {
                let metadata = place_ptr_metadata_operand(self, &place);
                *x = Rvalue::RawPtr {
                    place: place.clone(),
                    kind: *kind,
                    ptr_metadata: metadata,
                };
            }
            _ => {}
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
