//! Reconstruct rustc's `vec![..]` lowering based on `Box<MaybeUninit<[T; N]>>`.
//!
//! Rustc lowers `vec![elems...]` into something like:
//! ```ignore
//! let mut box = Box::new_uninit::<[T; N]>();
//! ((((*box)).1).0).0 = [elems...];
//! let vec = Box::box_assume_init_into_vec_unsafe::<T, N>(box);
//! ```
//! The last function is internally unsafe, although its signature is safe. It is
//! lowered this way for performance, which is not a concern here. Instead, we thus
//! rewrite this into something safe:
//! ```ignore
//! let box_uninit = Box::new_uninit::<[T; N]>();
//! let arr = [elems...];
//! let box_arr = Box::write::<[T; N]>(box_uninit, arr);
//! let box_slice = box_arr as Box<[T]>;
//! let vec = box_slice.into_vec();
//! ```
//!
//! See also: https://github.com/rust-lang/rust/pull/148190

use itertools::Itertools;

use crate::transform::TransformCtx;
use crate::transform::ctx::UllbcPass;
use crate::ullbc_ast::*;

const LANG_ITEM_BOX_ASSUME_INIT_INTO_VEC_UNSAFE: &'static str = "box_assume_init_into_vec_unsafe";

pub struct Transform;

#[derive(PartialEq, Eq)]
struct Rewrite {
    drop_bid: BlockId,
    target_bid: BlockId,
    payload_bid: BlockId,
    payload_idx: usize,
    move_bid: BlockId,
    move_idx: usize,
    span: Span,
    payload_elems: Vec<Operand>,
    elem_ty: Ty,
    len: Box<ConstantExpr>,
    alloc_ty: Option<Ty>,
    uninit_box: Place,
    vec_dest: Place,
    drop_on_unwind: BlockId,
}

impl Ord for Rewrite {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.drop_bid.cmp(&other.drop_bid)
    }
}

impl PartialOrd for Rewrite {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

fn is_assume_init_into_vec_call(ctx: &TransformCtx, call: &Call) -> bool {
    if let FnOperand::Regular(fn_ptr) = &call.func
        && let FnPtrKind::Fun(FunId::Regular(fid)) = *fn_ptr.kind
        && let Some(decl) = ctx.translated.fun_decls.get(fid)
    {
        decl.item_meta.lang_item.as_deref() == Some(LANG_ITEM_BOX_ASSUME_INIT_INTO_VEC_UNSAFE)
    } else {
        false
    }
}

fn box_inner_and_alloc(ty: &Ty) -> Option<(Ty, Option<Ty>)> {
    let TyKind::Adt(TypeDeclRef {
        id: TypeId::Builtin(BuiltinTy::Box),
        generics,
    }) = ty.kind()
    else {
        return None;
    };
    let inner = generics.types[TypeVarId::from_usize(0)].clone();
    let alloc = generics.types.get(TypeVarId::from_usize(1)).cloned();
    Some((inner, alloc))
}

fn mk_generics(ty0: Ty, ty1: Option<Ty>) -> GenericArgs {
    match ty1 {
        None => GenericArgs::new_types([ty0].into()),
        Some(ty1) => GenericArgs::new_types([ty0, ty1].into()),
    }
}

fn mk_box_ty(inner: Ty, alloc: Option<Ty>) -> Ty {
    TyKind::Adt(TypeDeclRef::new(
        TypeId::Builtin(BuiltinTy::Box),
        mk_generics(inner, alloc),
    ))
    .into_ty()
}

/// Given `src`, find the *unique* statement in the body of the form `src = [elems...]`
/// where the rvalue is an array aggregate.
/// Returns:
/// - the block and statement indices of the statement
/// - the span of the statement
/// - the operands of the array aggregate
/// - the element type and length of the array
fn find_array_assign(
    body: &ExprBody,
    src_local: LocalId,
) -> Option<(BlockId, usize, Span, Vec<Operand>, Ty, Box<ConstantExpr>)> {
    let mut out = None;
    for bid in body.body.all_indices() {
        for (idx, st) in body.body[bid].statements.iter().enumerate() {
            if let Some((place, Rvalue::Aggregate(AggregateKind::Array(elem_ty, len), elems))) =
                st.kind.as_assign()
                && place.local_id() == Some(src_local)
            {
                if out.is_some() {
                    return None;
                }

                out = Some((
                    bid,
                    idx,
                    st.span,
                    elems.clone(),
                    elem_ty.clone(),
                    len.clone(),
                ));
            };
        }
    }
    out
}

/// Given `src` and `dst`, find the *unique* statement in the body of the form `dst = move src`.
/// Return its block and statement indices, and `None` if there is no such statement, or if there are multiple.
fn find_move_into(body: &ExprBody, src_local: LocalId, dst: &Place) -> Option<(BlockId, usize)> {
    let mut out = None;
    for bid in body.body.all_indices() {
        for (idx, st) in body.body[bid].statements.iter().enumerate() {
            if let Some((dst_place, Rvalue::Use(Operand::Move(src_place)))) = st.kind.as_assign()
                && dst_place == dst
                && src_place.local_id() == Some(src_local)
            {
                if out.is_some() {
                    return None;
                }
                out = Some((bid, idx));
            }
        }
    }
    out
}

impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.treat_box_as_builtin
    }

    fn transform_body(&self, ctx: &mut TransformCtx, body: &mut ExprBody) {
        // We are looking for, in (flattened) ULLBC:
        //
        // dropped_box = [payload_elems...]: [elem_ty; len]
        // init_box = move dropped_box
        // drop (dropped_box)
        // vec_dest = box_assume_init_into_vec_unsafe(init_box)

        let rewrites = body.body.all_indices().filter_map(|bid| {
            // drop (dropped_box)
            let (_kind, dropped_box, _trait_ref, target, on_unwind) =
                body.body[bid].terminator.kind.as_drop()?;
            // check dropped_box: Box<MaybeUninit<_>>
            let (maybe_uninit_array_ty, alloc_ty) = box_inner_and_alloc(dropped_box.ty())?;
            let mu_decl = &ctx.translated.type_decls[maybe_uninit_array_ty.as_adt_id()?];
            if mu_decl.item_meta.lang_item.as_deref() != Some("maybe_uninit") {
                return None;
            };
            let dropped_box_l = dropped_box.local_id()?;

            // vec_dest = box_assume_init_into_vec_unsafe(init_box)
            let target_block = &body.body[*target];
            let (call, _tgt, _unwind) = &target_block.terminator.kind.as_call()?;

            if !is_assume_init_into_vec_call(ctx, call) {
                return None;
            }
            let [Operand::Move(init_box)] = call.args.as_slice() else {
                return None;
            };

            // dropped_box = [payload_elems...]: [elem_ty; len]
            let (payload_bid, payload_idx, span, payload_elems, elem_ty, len) =
                find_array_assign(body, dropped_box_l)?;

            // init_box = move dropped_box
            let (move_bid, move_idx) = find_move_into(body, dropped_box_l, init_box)?;

            Some(Rewrite {
                drop_bid: bid,
                target_bid: *target,
                payload_bid,
                payload_idx,
                move_bid,
                move_idx,
                span,
                payload_elems,
                elem_ty,
                len,
                alloc_ty,
                uninit_box: dropped_box.clone(),
                vec_dest: call.dest.clone(),
                drop_on_unwind: *on_unwind,
            })
        });

        for rw in rewrites.sorted() {
            let array_ty = Ty::mk_array(rw.elem_ty.clone(), *rw.len.clone());
            let array_local = body.locals.new_var(None, array_ty.clone());
            let box_array_ty = mk_box_ty(array_ty.clone(), rw.alloc_ty.clone());
            let box_slice_ty = mk_box_ty(Ty::mk_slice(rw.elem_ty.clone()), rw.alloc_ty.clone());
            let box_array_local = body.locals.new_var(None, box_array_ty.clone());
            let box_slice_local = body.locals.new_var(None, box_slice_ty.clone());

            let array_lid = array_local.as_local().unwrap();
            let box_array_lid = box_array_local.as_local().unwrap();
            let box_slice_lid = box_slice_local.as_local().unwrap();

            body.body[rw.move_bid].statements[rw.move_idx].kind = StatementKind::Nop;

            body.body[rw.payload_bid].statements.splice(
                rw.payload_idx..=rw.payload_idx,
                [
                    StatementKind::StorageLive(array_lid),
                    StatementKind::Assign(
                        array_local.clone(),
                        Rvalue::Aggregate(
                            AggregateKind::Array(rw.elem_ty.clone(), rw.len.clone()),
                            rw.payload_elems,
                        ),
                    ),
                ]
                .map(|k| Statement::new(rw.span, k)),
            );

            let drop_block = &mut body.body[rw.drop_bid];
            drop_block.statements.push(Statement::new(
                rw.span,
                StatementKind::StorageLive(box_array_lid),
            ));

            drop_block.terminator.kind = TerminatorKind::Call {
                call: Call {
                    func: FnOperand::Regular(FnPtr::new(
                        FnPtrKind::Fun(FunId::Builtin(BuiltinFunId::BoxWrite)),
                        mk_generics(array_ty, rw.alloc_ty.clone()),
                    )),
                    args: vec![
                        Operand::Move(rw.uninit_box),
                        Operand::Move(array_local.clone()),
                    ],
                    dest: box_array_local.clone(),
                },
                target: rw.target_bid,
                on_unwind: rw.drop_on_unwind,
            };

            let target_block = &mut body.body[rw.target_bid];

            target_block.statements.splice(
                0..0,
                [
                    StatementKind::StorageDead(array_lid),
                    StatementKind::StorageLive(box_slice_lid),
                    StatementKind::Assign(
                        box_slice_local.clone(),
                        Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::Unsize(
                                box_array_ty,
                                box_slice_ty,
                                UnsizingMetadata::Length(rw.len),
                            )),
                            Operand::Move(box_array_local),
                        ),
                    ),
                ]
                .map(|k| Statement::new(rw.span, k)),
            );

            let (target_call, _, _) = target_block.terminator.kind.as_call_mut().unwrap();

            *target_call = Call {
                func: FnOperand::Regular(FnPtr::new(
                    FnPtrKind::Fun(FunId::Builtin(BuiltinFunId::SliceIntoVec)),
                    mk_generics(rw.elem_ty, rw.alloc_ty),
                )),
                args: vec![Operand::Move(box_slice_local)],
                dest: rw.vec_dest,
            };
        }
    }
}
