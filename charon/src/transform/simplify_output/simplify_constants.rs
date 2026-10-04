//! The MIR constant expressions lead to a lot of duplication: there are
//! for instance constant ADTs which duplicate the "regular" aggregated
//! ADTs in the operands, constant references, etc. This reduces the number
//! of cases to handle and eases the function translation in Aeneas.
//!
//! This pass removes all those occurrences, leaving only primitive constant expressions. It does
//! so by introducing intermediate statements.
//!
//! A small remark about the intermediate statements we introduce for the globals:
//! we do so because, when evaluating the code in "concrete" mode, it allows to
//! handle the globals like function calls.

use itertools::Itertools;

use crate::transform::TransformCtx;
use crate::transform::ctx::{BodyTransformCtx, UllbcPass, UllbcStatementTransformCtx};
use crate::ullbc_ast::*;

/// Add a global holding `value`, named like the promoted constants of the current item, and return its place.
/// `ptr_metadata` is the metadata of pointers to the global.
fn new_promoted_global(
    ctx: &mut UllbcStatementTransformCtx<'_>,
    value: ConstantExpr,
    ptr_metadata: ConstantExpr,
) -> GlobalDeclRef {
    let krate = &mut ctx.ctx.translated;
    let id = ItemId::Fun(*ctx.def_id);
    let mut name = krate.item_names.get(&id).unwrap().clone();
    let promoted_count = krate
        .item_names
        .values()
        .filter_map(|n| n.name.split_last())
        .filter(|(last, prefix)| {
            matches!(last, PathElem::Builtin(BuiltinPathElem::PromotedConst, _))
                && *prefix == name.name.as_slice()
        })
        .count();
    let disambiguator = Disambiguator::new(promoted_count);
    name.name.push(PathElem::Builtin(
        BuiltinPathElem::PromotedConst,
        disambiguator,
    ));
    let ty = value.ty().clone();
    let id = krate.global_decls.push_with(|def_id| GlobalDecl {
        def_id,
        item_meta: ItemMeta::dummy_public(ctx.span, name.clone(), true, ItemOpacity::Transparent),
        generics: GenericParams::empty(),
        ty: ty.clone(),
        size: Size::from_expr(SizeExpr::size_of(&ty)),
        align: Size::from_expr(SizeExpr::align_of(&ty)),
        ptr_metadata,
        src: GlobalSource::Normal,
        global_kind: GlobalKind::AnonConst,
        value,
    });
    krate.item_names.insert(id.into(), name);
    GlobalDeclRef {
        id,
        generics: Box::new(GenericArgs::empty()),
    }
}

/// If the constant value is a constant ADT, push `Assign::Aggregate` statements
/// to the vector of statements, that bind new variables to the ADT parts and
/// the variable assigned to the complete ADT.
///
/// Goes fom e.g. `f(T::A(x, y))` to `let a = T::A(x, y); f(a)`.
/// The function is recursively called on the aggregate fields (e.g. here x and y).
fn transform_constant_expr(
    ctx: &mut UllbcStatementTransformCtx<'_>,
    mut val: ConstantExpr,
) -> Operand {
    let rval = match val.kind() {
        // Here we use a copy, rather than a move -- moving a global would leave it uninitialized.
        ConstantExprKind::Global(global_ref) => {
            return Operand::Copy(Place::new_global(global_ref.clone(), val.ty().clone()));
        }
        ConstantExprKind::PtrNoProvenance(ptr) => {
            let usize_ty = Ty::mk_usize();
            let ptr_usize = ConstantExprKind::Integer(IntegerValue::Unsigned(UIntTy::Usize, *ptr));
            let cast = UnOp::Cast(CastKind::RawPtr(usize_ty.clone(), val.ty().clone()));
            Rvalue::UnaryOp(cast, Operand::Const(ConstantExpr::new(ptr_usize, usize_ty)))
        }
        cexpr @ (ConstantExprKind::Ref(bval, metadata)
        | ConstantExprKind::Ptr(_, bval, metadata)) => {
            let rk = cexpr.as_ptr().map(|(rk, _, _)| *rk);
            let bval_is_sized = bval.ty().get_ptr_metadata(ctx.get_crate()).is_none();

            let place = match bval.kind() {
                ConstantExprKind::Global(global_ref) => {
                    Place::new_global(global_ref.clone(), bval.ty().clone())
                }
                // A local can't be unsized, so we put it in a new global
                _ if !bval_is_sized => {
                    let meta = match metadata.as_ref().unwrap() {
                        UnsizingMetadata::Length(meta) | UnsizingMetadata::VTable(_, meta) => meta,
                        UnsizingMetadata::VTableUpcast(..) | UnsizingMetadata::Unknown => {
                            unreachable!("unexpected const metadata")
                        }
                    };
                    let global_ref = new_promoted_global(ctx, bval.clone(), meta.clone());
                    Place::new_global(global_ref, bval.ty().clone())
                }
                _ => {
                    // Recurse on the borrowed value
                    let bval = transform_constant_expr(ctx, bval.clone());

                    // Evaluate the referenced value
                    let bval_ty = bval.ty().clone();
                    ctx.rval_to_place(Rvalue::Use(bval, WithRetag::No), bval_ty)
                }
            };
            // A sized place is unsized after being borrowed, if there's metadata.
            let mut rval = match (rk, metadata.clone().filter(|_| bval_is_sized)) {
                // Borrow the place.
                (None, None) => ctx.borrow(place, BorrowKind::Shared),
                (Some(rk), None) => ctx.raw_borrow(place, rk),
                // Unsizing borrow.
                (None, Some(metadata)) => {
                    let sized_ref = ctx.borrow_to_new_var(place, BorrowKind::Shared, None);
                    Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::Unsize(
                            sized_ref.ty.clone(),
                            val.ty().clone(),
                            metadata,
                        )),
                        Operand::Move(sized_ref),
                    )
                }
                (Some(rk), Some(metadata)) => {
                    let sized_raw_ref = ctx.raw_borrow_to_new_var(place, rk, None);
                    Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::Unsize(
                            sized_raw_ref.ty.clone(),
                            val.ty().clone(),
                            metadata,
                        )),
                        Operand::Move(sized_raw_ref),
                    )
                }
            };
            // The metadata of an unsized global may be a vtable reference, which we lower too.
            if let Rvalue::Ref { ptr_metadata, .. } | Rvalue::RawPtr { ptr_metadata, .. } =
                &mut rval
            {
                transform_operand(ctx, ptr_metadata);
            }
            rval
        }
        ConstantExprKind::Adt(..) if val.ty().is_unit() => {
            // Keep unit constants to avoid adding countless unit locals.
            return Operand::Const(val);
        }
        ConstantExprKind::Adt(variant, fields) => {
            let fields = fields
                .iter()
                .cloned()
                .map(|x| transform_constant_expr(ctx, x))
                .collect();

            // Build an `Aggregate` rvalue.
            let tref = val.ty().kind().as_adt().unwrap();
            let aggregate_kind = AggregateKind::Adt(tref.clone(), *variant, None);
            Rvalue::Aggregate(aggregate_kind, fields)
        }
        ConstantExprKind::Array(fields)
            if let TyKind::Array(ty, _, ty_is_sized) = val.ty().kind() =>
        {
            let fields = fields
                .iter()
                .cloned()
                .map(|x| transform_constant_expr(ctx, x))
                .collect_vec();
            let len = ConstantExpr::mk_usize(fields.len() as u128);
            Rvalue::Aggregate(
                AggregateKind::Array(ty.clone(), len, ty_is_sized.clone()),
                fields,
            )
        }
        ConstantExprKind::FnPtr(fptr) if let TyKind::FnPtr(sig) = val.ty().kind() => {
            let from_ty =
                TyKind::FnDef(sig.clone().map(|_| fptr.clone().move_under_binder())).into_ty();
            let to_ty = TyKind::FnPtr(sig.clone()).into_ty();
            Rvalue::UnaryOp(
                UnOp::Cast(CastKind::FnPtr(from_ty.clone(), to_ty)),
                Operand::Const(ConstantExpr::new(
                    ConstantExprKind::FnDef(fptr.clone()),
                    from_ty,
                )),
            )
        }
        ConstantExprKind::Cast(value, target_ty) => {
            let source_ty = value.ty().clone();
            let target_ty = target_ty.clone();
            let value = transform_constant_expr(ctx, value.clone());
            let cast_kind = if source_ty.is_fn_ptr() | source_ty.is_fn_def() {
                CastKind::FnPtr(source_ty, target_ty)
            } else {
                CastKind::RawPtr(source_ty, target_ty)
            };
            Rvalue::UnaryOp(UnOp::Cast(cast_kind), value)
        }
        ConstantExprKind::VTableRef(tref)
            if let Some(vtable_ref) = tref.vtable_ref(&ctx.ctx.translated)
                && let TyKind::Ref(_, vtable_ty, _) = val.ty().kind() =>
        {
            let inner = ConstantExpr::new(
                ConstantExprKind::Global(vtable_ref.clone()),
                vtable_ty.clone(),
            );
            val.with_contents_mut(|kind, _| *kind = ConstantExprKind::Ref(inner, None));
            // Normalize further into a place access.
            return transform_constant_expr(ctx, val);
        }
        _ => return Operand::Const(val),
    };
    Operand::Move(ctx.rval_to_place(rval, val.ty().clone()))
}

fn transform_operand(ctx: &mut UllbcStatementTransformCtx<'_>, op: &mut Operand) {
    // Transform the constant operands (otherwise do nothing)
    take_mut::take(op, |op| {
        if let Operand::Const(val) = op {
            transform_constant_expr(ctx, val)
        } else {
            op
        }
    })
}

pub struct Transform;
impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        !options.raw_consts
    }

    fn transform_function(&self, ctx: &mut TransformCtx, fun_decl: &mut FunDecl) {
        fun_decl.transform_ullbc_operands(ctx, transform_operand);
        if let Some(body) = fun_decl.body.as_unstructured_mut() {
            for block in body.body.iter_mut() {
                // Normalize unit constants into unit aggregates.
                block.dyn_visit_in_body_mut(|rvalue: &mut Rvalue| {
                    take_mut::take(rvalue, |rvalue| match rvalue {
                        Rvalue::Use(Operand::Const(e), _)
                            if e.kind().is_adt() && e.ty().is_unit() =>
                        {
                            Rvalue::unit_value()
                        }
                        _ => rvalue,
                    });
                });
            }
        }
    }
}
