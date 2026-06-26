//! Reconstruct rustc's `vec![..]` lowering based on `Box<MaybeUninit<[T; N]>>`.
//!
//! In `inline_selected_functions`, we inline the special `box_assume_init_into_vec_unsafe`
//! function. After that, a `vec![elems...]` expression ends up looking something like:
//! ```ignore
//! let mut box = Box::new_uninit::<[T; N]>();
//! (((*box).1).0).0 = [elems...];
//! let box = Box::assume_init(box);
//! ..
//! ```
//! The split between assignment and `assume_init` is for performance. The `assume_init` call is
//! unsafe, so we rewrite it to use `Box::write` instead, and even `Box::new` if possible.
//! ```ignore
//! let box_uninit = Box::new_uninit::<[T; N]>();
//! let arr = [elems...];
//! let box = Box::write::<[T; N]>(box_uninit, arr);
//! ..
//! ```
//!
//! See also: <https://github.com/rust-lang/rust/pull/148190>

use itertools::Itertools;
use std::collections::HashSet;

use crate::ast::ullbc_ast_utils::StmtLoc;
use crate::name_matcher::NamePattern;
use crate::transform::ctx::UllbcPass;
use crate::transform::{CowBox, TransformCtx};
use crate::ullbc_ast::*;

pub struct Transform {
    box_write: Option<FunDeclId>,
}

struct Rewrite {
    new_uninit_bid: BlockId,
    new_uninit_target: BlockId,
    drop_bid: BlockId,
    target_bid: BlockId,
    payload_loc: StmtLoc,
    move_loc: StmtLoc,
    arg_move_loc: StmtLoc,
    span: Span,
    payload_elems: Vec<Operand>,
    elem_ty: Ty,
    len: Box<ConstantExpr>,
    uninit_box: Place,
    branched_before_payload: bool,
    box_array: Place,
    box_array_generics: GenericArgs,
    assume_init_generics: GenericArgs,
    drop_on_unwind: BlockId,
    assume_init_target: BlockId,
}

struct PayloadAssign {
    loc: StmtLoc,
    span: Span,
    payload_elems: Vec<Operand>,
    elem_ty: Ty,
    len: Box<ConstantExpr>,
    branched_before_payload: bool,
}

struct AssumeInitTail {
    move_loc: StmtLoc,
    drop_bid: BlockId,
    target_bid: BlockId,
    arg_move_loc: StmtLoc,
    box_array: Place,
    assume_init_generics: GenericArgs,
    drop_on_unwind: BlockId,
    assume_init_target: BlockId,
}

fn assume_init_fn_ptr<'a>(ctx: &TransformCtx, call: &'a Call) -> Option<&'a FnPtr> {
    if let FnOperand::Regular(fn_ptr) = &call.func
        && let FnPtrKind::Fun(FunId::Regular(fid)) = *fn_ptr.kind
        && ctx.translated.item_name(fid).short_str() == Some("assume_init")
    {
        Some(fn_ptr)
    } else {
        None
    }
}

fn box_inner(ty: &Ty) -> Option<Ty> {
    let TyKind::Adt(TypeDeclRef {
        id: TypeId::Builtin(BuiltinTy::Box),
        generics,
    }) = ty.kind()
    else {
        return None;
    };
    Some(generics.types[TypeVarId::from_usize(0)].clone())
}

fn box_generics(ty: &Ty) -> Option<GenericArgs> {
    let TyKind::Adt(TypeDeclRef {
        id: TypeId::Builtin(BuiltinTy::Box),
        generics,
    }) = ty.kind()
    else {
        return None;
    };
    Some((**generics).clone())
}

/// Given `src`, find the unique statement of the form `src = [elems...]`
/// where the rvalue is an array aggregate.
///
/// Also returns whether a straight-line path from `start` hits a branch before reaching the
/// assignment. We ignore unwind edges; this matches the later rewrite's ability to erase the
/// allocation when the normal path to initialization is linear.
fn find_array_assign(body: &ExprBody, start: BlockId, src_local: LocalId) -> Option<PayloadAssign> {
    let mut out = None;
    for (bid, block) in body.body.iter_enumerated() {
        for (idx, st) in block.statements.iter().enumerate() {
            let Some((place, Rvalue::Aggregate(AggregateKind::Array(elem_ty, len), elems))) =
                st.kind.as_assign()
            else {
                continue;
            };
            if place.local_id() != Some(src_local) {
                continue;
            }
            if out.is_some() {
                return None;
            }

            let loc = StmtLoc::new(bid, idx);
            out = Some(PayloadAssign {
                loc,
                span: st.span,
                payload_elems: elems.clone(),
                elem_ty: elem_ty.clone(),
                len: len.clone(),
                branched_before_payload: branched_before(body, start, loc.block)?,
            });
        }
    }
    out
}

fn branched_before(body: &ExprBody, start: BlockId, target: BlockId) -> Option<bool> {
    let mut block_id = start;
    let mut visited = HashSet::new();
    while visited.insert(block_id) {
        if block_id == target {
            return Some(false);
        }

        let block = &body.body[block_id];
        let targets = block.targets_ignoring_unwind();
        if targets.len() > 1 {
            return Some(true);
        }
        block_id = targets.into_iter().exactly_one().ok()?;
    }
    None
}

fn unique_target(term: &Terminator) -> Option<BlockId> {
    term.targets_ignoring_unwind()
        .into_iter()
        .exactly_one()
        .ok()
}

fn find_next_move_of(
    body: &ExprBody,
    mut cursor: StmtLoc,
    src: &Place,
) -> Option<(StmtLoc, Place)> {
    let mut visited = HashSet::new();
    while visited.insert(cursor) {
        let block = &body.body[cursor.block];
        while cursor.statement < block.statements.len() {
            let st = &body[cursor];
            if let Some((dst_place, Rvalue::Use(Operand::Move(src_place), _))) = st.kind.as_assign()
                && src_place == src
            {
                return Some((cursor, dst_place.clone()));
            }
            cursor = cursor.after();
        }
        cursor = StmtLoc::block_start(unique_target(&block.terminator)?);
    }
    None
}

fn find_next_drop(
    body: &ExprBody,
    mut block_id: BlockId,
    dropped_place: &Place,
) -> Option<(BlockId, BlockId, BlockId)> {
    let mut visited = HashSet::new();
    while visited.insert(block_id) {
        let block = &body.body[block_id];
        if let TerminatorKind::Drop {
            place: dropped,
            target,
            on_unwind,
            ..
        } = &block.terminator.kind
            && dropped == dropped_place
        {
            return Some((block_id, *target, *on_unwind));
        }
        block_id = unique_target(&block.terminator)?;
    }
    None
}

fn find_move_in_block(
    body: &ExprBody,
    block: BlockId,
    src: &Place,
    dst: &Place,
) -> Option<StmtLoc> {
    let mut out = None;
    for (statement, st) in body.body[block].statements.iter().enumerate() {
        if let Some((dst_place, Rvalue::Use(Operand::Move(src_place), _))) = st.kind.as_assign()
            && dst_place == dst
            && src_place == src
        {
            if out.is_some() {
                return None;
            }
            out = Some(StmtLoc::new(block, statement));
        }
    }
    out
}

fn find_assume_init_tail(
    ctx: &TransformCtx,
    body: &ExprBody,
    cursor: StmtLoc,
    uninit_box: &Place,
) -> Option<AssumeInitTail> {
    let (move_loc, moved_box) = find_next_move_of(body, cursor, uninit_box)?;
    let (drop_bid, target_bid, drop_on_unwind) = find_next_drop(body, move_loc.block, uninit_box)?;

    let target_block = &body.body[target_bid];
    let (call, assume_init_target, _unwind) = target_block.terminator.kind.as_call()?;
    let assume_init_fn = assume_init_fn_ptr(ctx, call)?;
    let [Operand::Move(init_box)] = call.args.as_slice() else {
        return None;
    };
    let arg_move_loc = find_move_in_block(body, target_bid, &moved_box, init_box)?;

    Some(AssumeInitTail {
        move_loc,
        drop_bid,
        target_bid,
        arg_move_loc,
        box_array: call.dest.clone(),
        assume_init_generics: assume_init_fn.generics.as_ref().clone(),
        drop_on_unwind,
        assume_init_target: *assume_init_target,
    })
}

fn is_new_uninit_call(ctx: &TransformCtx, call: &Call) -> bool {
    if !call.args.is_empty() {
        return false;
    }

    let FnOperand::Regular(fn_ptr) = &call.func else {
        return false;
    };
    let FnPtrKind::Fun(FunId::Regular(fid)) = *fn_ptr.kind else {
        return false;
    };
    ctx.translated.item_name(fid).short_str() == Some("new_uninit")
}

impl Transform {
    pub fn new(ctx: &mut TransformCtx) -> CowBox<dyn UllbcPass> {
        let pat = NamePattern::parse(crate::builtins::BOX_WRITE_PATTERN).unwrap();
        let box_write = ctx
            .translated
            .item_names
            .iter()
            .filter(|(_, name)| pat.matches(&ctx.translated, name))
            .filter_map(|(id, _)| id.as_fun())
            .copied()
            .exactly_one()
            .ok();
        CowBox::Owned(Box::new(Transform { box_write }))
    }
}

impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.treat_box_as_builtin && !options.monomorphize_with_hax && self.box_write.is_some()
    }

    fn transform_body(&self, ctx: &mut TransformCtx, body: &mut ExprBody) {
        // Checked in `should_run`
        let box_write = self.box_write.unwrap();

        // We are looking for, in (flattened) ULLBC:
        //
        // box1 = new_uninit()
        // ...
        // ((((*box1)).1).0).0 = [move _4]
        // box2 = move box1
        // conditional_drop box1
        // box3 = move box2
        // box4 = assume_init(move box3)
        let rewrites = body
            .body
            .iter_enumerated()
            .filter_map(|(new_uninit_bid, block)| {
                let TerminatorKind::Call {
                    call,
                    target: new_uninit_target,
                    ..
                } = &block.terminator.kind
                else {
                    return None;
                };

                if !is_new_uninit_call(ctx, call) {
                    return None;
                }
                // check uninit_box: Box<MaybeUninit<_>>
                let uninit_box = call.dest.clone();
                let maybe_uninit_array_ty = box_inner(uninit_box.ty())?;
                let mu_decl = &ctx
                    .translated
                    .type_decls
                    .get(maybe_uninit_array_ty.as_adt_id()?)?;
                if mu_decl.item_meta.lang_item.as_deref() != Some("maybe_uninit") {
                    return None;
                };
                let uninit_box_l = uninit_box.local_id()?;

                // (*uninit_box).1.0.0 = [payload_elems...]: [elem_ty; len]
                let payload = find_array_assign(body, *new_uninit_target, uninit_box_l)?;

                // assume_init(uninit_box2)
                let tail = find_assume_init_tail(ctx, body, payload.loc.after(), &uninit_box)?;
                let box_array_generics = box_generics(tail.box_array.ty())?;

                Some(Rewrite {
                    new_uninit_bid,
                    new_uninit_target: *new_uninit_target,
                    drop_bid: tail.drop_bid,
                    target_bid: tail.target_bid,
                    payload_loc: payload.loc,
                    move_loc: tail.move_loc,
                    arg_move_loc: tail.arg_move_loc,
                    span: payload.span,
                    payload_elems: payload.payload_elems,
                    elem_ty: payload.elem_ty,
                    len: payload.len,
                    uninit_box,
                    branched_before_payload: payload.branched_before_payload,
                    box_array_generics,
                    assume_init_generics: tail.assume_init_generics,
                    drop_on_unwind: tail.drop_on_unwind,
                    box_array: tail.box_array,
                    assume_init_target: tail.assume_init_target,
                })
            });

        for rw in rewrites.collect::<Vec<_>>() {
            let array_ty = Ty::mk_array(rw.elem_ty.clone(), *rw.len.clone());
            let array_local = body.locals.new_var(None, array_ty.clone());
            let box_array_ty = rw.box_array.ty().clone();
            let box_array_local = body.locals.new_var(None, box_array_ty.clone());

            let array_lid = array_local.as_local().unwrap();
            let box_array_lid = box_array_local.as_local().unwrap();

            body[rw.move_loc].kind = StatementKind::Nop;
            body[rw.arg_move_loc].kind = StatementKind::Nop;

            body.body[rw.payload_loc.block].statements.splice(
                rw.payload_loc.statement..=rw.payload_loc.statement,
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

            let (fn_ptr, args) = if rw.branched_before_payload {
                (
                    FnPtr::new(
                        FnPtrKind::Fun(FunId::Regular(box_write)),
                        rw.assume_init_generics,
                    ),
                    vec![
                        Operand::Move(rw.uninit_box),
                        Operand::Move(array_local.clone()),
                    ],
                )
            } else {
                body.body[rw.new_uninit_bid].terminator.kind = TerminatorKind::Goto {
                    target: rw.new_uninit_target,
                };
                (
                    FnPtr::new(
                        FnPtrKind::Fun(FunId::Builtin(BuiltinFunId::BoxNew)),
                        rw.box_array_generics,
                    ),
                    vec![Operand::Move(array_local.clone())],
                )
            };

            let drop_block = &mut body.body[rw.drop_bid];
            drop_block.statements.push(Statement::new(
                rw.span,
                StatementKind::StorageLive(box_array_lid),
            ));
            drop_block.terminator.kind = TerminatorKind::Call {
                call: Call {
                    func: FnOperand::Regular(fn_ptr),
                    args,
                    dest: box_array_local.clone(),
                },
                target: rw.target_bid,
                on_unwind: rw.drop_on_unwind,
            };

            let target_block = &mut body.body[rw.target_bid];
            target_block.statements.push(Statement::new(
                rw.span,
                StatementKind::StorageDead(array_lid),
            ));
            target_block.statements.push(Statement::new(
                rw.span,
                StatementKind::Assign(
                    rw.box_array,
                    Rvalue::Use(Operand::Move(box_array_local), WithRetag::No),
                ),
            ));
            target_block.statements.push(Statement::new(
                rw.span,
                StatementKind::StorageDead(box_array_lid),
            ));
            target_block.terminator.kind = TerminatorKind::Goto {
                target: rw.assume_init_target,
            };
        }
    }
}
