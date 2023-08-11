//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

#![allow(dead_code)]
use crate::assumed;
use crate::common::*;
use crate::expressions as e;
use crate::formatter::Formatter;
use crate::generics;
use crate::get_mir::{boxes_are_desugared, get_mir_for_def_id_and_level};
use crate::id_vector;
use crate::names_utils::def_id_to_name;
use crate::regions_hierarchy::RegionGroups;
use crate::translate_ctx::*;
use crate::translate_types;
use crate::types as ty;
use crate::types::{FieldId, VariantId};
use crate::ullbc_ast as ast;
use crate::values as v;
use crate::values::{Literal, ScalarValue};
use core::convert::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use log::warn;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir::START_BLOCK;
use rustc_middle::ty as mir_ty;
use rustc_middle::ty::{TyCtxt, TyKind};
use std::iter::FromIterator;
use translate_types::{translate_erased_region, translate_region_name};

fn translate_variant_id(id: hax::VariantIdx) -> VariantId::Id {
    VariantId::Id::new(id)
}

fn translate_field_id(id: hax::FieldIdx) -> FieldId::Id {
    use rustc_index::Idx;
    FieldId::Id::new(id.index())
}

/// Translate a `BorrowKind`
fn translate_borrow_kind(borrow_kind: hax::BorrowKind) -> e::BorrowKind {
    match borrow_kind {
        hax::BorrowKind::Shared => e::BorrowKind::Shared,
        hax::BorrowKind::Mut {
            allow_two_phase_borrow,
        } => {
            if allow_two_phase_borrow {
                e::BorrowKind::TwoPhaseMut
            } else {
                e::BorrowKind::Mut
            }
        }
        hax::BorrowKind::Unique => {
            unimplemented!();
        }
        hax::BorrowKind::Shallow => e::BorrowKind::Shallow,
    }
}

fn translate_binaryop_kind(binop: hax::BinOp) -> e::BinOp {
    use hax::BinOp;
    match binop {
        BinOp::BitXor => e::BinOp::BitXor,
        BinOp::BitAnd => e::BinOp::BitAnd,
        BinOp::BitOr => e::BinOp::BitOr,
        BinOp::Eq => e::BinOp::Eq,
        BinOp::Lt => e::BinOp::Lt,
        BinOp::Le => e::BinOp::Le,
        BinOp::Ne => e::BinOp::Ne,
        BinOp::Ge => e::BinOp::Ge,
        BinOp::Gt => e::BinOp::Gt,
        BinOp::Div => e::BinOp::Div,
        BinOp::Rem => e::BinOp::Rem,
        BinOp::Add => e::BinOp::Add,
        BinOp::Sub => e::BinOp::Sub,
        BinOp::Mul => e::BinOp::Mul,
        BinOp::Shl => e::BinOp::Shl,
        BinOp::Shr => e::BinOp::Shr,
        _ => {
            unreachable!();
        }
    }
}

fn translate_unaryop_kind(binop: hax::UnOp) -> e::UnOp {
    use hax::UnOp;
    match binop {
        UnOp::Not => e::UnOp::Not,
        UnOp::Neg => e::UnOp::Neg,
    }
}

/// Build an uninterpreted constant from a MIR constant identifier.
fn rid_as_unevaluated_constant<'tcx>(id: DefId) -> rustc_middle::mir::UnevaluatedConst<'tcx> {
    let p = mir_ty::List::empty();
    rustc_middle::mir::UnevaluatedConst::new(id, p)
}

/// A function definition can be top-level, or can be defined in an `impl`
/// block. In this case, we might want to retrieve the type for which the
/// impl block was defined. This function returns this type's def id if
/// the function def id given as input was defined in an impl block, and
/// returns `None` otherwise.
///
/// For instance, when translating `bar` below:
/// ```text
/// impl Foo {
///     fn bar(...) -> ... { ... }
/// }
/// ```
/// we might want to know that `bar` is actually defined in one of `Foo`'s impl
/// blocks (and retrieve `Foo`'s identifier).
///
/// TODO: this might gives us the same as TyCtxt::generics_of
fn get_impl_parent_type_def_id(tcx: TyCtxt, def_id: DefId) -> Option<DefId> {
    // Retrieve the definition def id
    let def_key = tcx.def_key(def_id);

    // Reconstruct the parent def id: it's the same as the function's def id,
    // at the exception of the index.
    let parent_def_id = DefId {
        index: def_key.parent.unwrap(),
        ..def_id
    };

    // Retrieve the parent's key
    let parent_def_key = tcx.def_key(parent_def_id);

    // Match on the parent key
    let parent = match parent_def_key.disambiguated_data.data {
        rustc_hir::definitions::DefPathData::Impl => {
            // Parent is an impl block! Retrieve the type definition (it
            // seems that `type_of` is the only way of getting it)
            let parent_type = tcx.type_of(parent_def_id).subst_identity();

            // The parent type should be ADT
            match parent_type.kind() {
                rustc_middle::ty::TyKind::Adt(adt_def, _) => Some(adt_def.did()),
                _ => {
                    unreachable!();
                }
            }
        }
        _ => {
            // Not an impl block
            None
        }
    };

    // TODO: checking
    assert!(parent == tcx.generics_of(def_id).parent);

    parent
}

/// Translate a call to a function considered primitive and which is not:
/// panic, begin_panic, box_free (those have a *very* special treatment).
fn translate_primitive_function_call(
    tcx: TyCtxt<'_>,
    def_id: &hax::DefId,
    region_args: Vec<ty::ErasedRegion>,
    type_args: Vec<ty::ETy>,
    const_generic_args: Vec<ty::ConstGeneric>,
    args: Vec<e::Operand>,
    dest: e::Place,
    target: ast::BlockId::Id,
) -> Result<ast::RawTerminator> {
    let rust_id = def_id.rust_def_id.unwrap();
    trace!("- def_id: {:?}", rust_id);

    // Translate the function name
    // TODO: replace
    let name = def_id_to_name(def_id);
    trace!("name: {}", name);

    // We assume the function has primitive support, and look up
    // its primitive identifier
    let aid = assumed::get_fun_id_from_name(&name, &type_args).unwrap();

    // Translate the function call
    // Note that some functions are actually traits (deref, index, etc.):
    // we assume that they are called only on a limited set of types
    // (ex.: box, vec...).
    // For those trait functions, we need a custom treatment to retrieve
    // and check the type information.
    // For instance, derefencing boxes generates MIR of the following form:
    // ```
    // _2 = <Box<u32> as Deref>::deref(move _3)
    // ```
    // We have to retrieve the type `Box<u32>` and check that it is of the
    // form `Box<T>` (and we generate `box_deref<u32>`).
    match aid {
        ast::AssumedFunId::Replace
        | ast::AssumedFunId::BoxNew
        | ast::AssumedFunId::VecNew
        | ast::AssumedFunId::VecPush
        | ast::AssumedFunId::VecInsert
        | ast::AssumedFunId::VecLen
        | ast::AssumedFunId::SliceLen => {
            let call = ast::Call {
                func: ast::FunId::Assumed(aid),
                region_args,
                type_args,
                const_generic_args,
                args,
                dest,
            };
            Ok(ast::RawTerminator::Call { call, target })
        }
        ast::AssumedFunId::BoxDeref | ast::AssumedFunId::BoxDerefMut => translate_box_deref(
            aid,
            region_args,
            type_args,
            const_generic_args,
            args,
            dest,
            target,
        ),
        ast::AssumedFunId::VecIndex | ast::AssumedFunId::VecIndexMut => translate_vec_index(
            aid,
            region_args,
            type_args,
            const_generic_args,
            args,
            dest,
            target,
        ),
        ast::AssumedFunId::ArraySubsliceShared
        | ast::AssumedFunId::ArraySubsliceMut
        | ast::AssumedFunId::SliceSubsliceShared
        | ast::AssumedFunId::SliceSubsliceMut => {
            // Take a subslice from an array/slice.
            // Note that this isn't any different from a regular function call. Ideally,
            // we'd have a generic assumed function mechanism.
            assert!(type_args.len() == 1);
            assert!(args.len() == 2);
            assert!(const_generic_args.is_empty());
            // We need to unwrap the type to retrieve the `T` inside the `Slice<T>`
            // or the `Array<T, N>`
            let (_, _, type_args, const_generic_args) = type_args[0].clone().to_adt();
            assert!(type_args.len() == 1);
            assert!(const_generic_args.len() <= 1);

            let call = ast::Call {
                func: ast::FunId::Assumed(aid),
                region_args,
                type_args,
                const_generic_args,
                args,
                dest,
            };

            Ok(ast::RawTerminator::Call { call, target })
        }
        ast::AssumedFunId::BoxFree => {
            // Special case handled elsewhere
            unreachable!();
        }
        ast::AssumedFunId::ArrayIndexShared
        | ast::AssumedFunId::ArrayIndexMut
        | ast::AssumedFunId::ArrayToSliceShared
        | ast::AssumedFunId::ArrayToSliceMut
        | ast::AssumedFunId::SliceIndexShared
        | ast::AssumedFunId::SliceIndexMut => {
            // Those cases are introduced later, in micro-passes, by desugaring
            // projections (for ArrayIndex and ArrayIndexMut for instnace) and=
            // operations (for ArrayToSlice for instance) to function calls.
            unreachable!()
        }
    }
}

/// Translate `std::Deref::deref` or `std::DerefMut::deref_mut` applied
/// on boxes. We need a custom function because it is a trait.
fn translate_box_deref(
    aid: ast::AssumedFunId,
    region_args: Vec<ty::ErasedRegion>,
    type_args: Vec<ty::ETy>,
    const_generic_args: Vec<ty::ConstGeneric>,
    args: Vec<e::Operand>,
    dest: e::Place,
    target: ast::BlockId::Id,
) -> Result<ast::RawTerminator> {
    // Check the arguments
    assert!(region_args.is_empty());
    assert!(type_args.len() == 1);
    assert!(args.len() == 1);

    // For now we only support deref on boxes
    // Retrieve the boxed value
    let arg_ty = type_args.get(0).unwrap(); // should be `Box<...>`
    let boxed_ty = arg_ty.as_box();
    if boxed_ty.is_none() {
        panic!(
            "Deref/DerefMut trait applied with parameter {:?} while it is only supported on Box<T> values",
            arg_ty
        );
    }
    let boxed_ty = boxed_ty.unwrap();
    let type_args = vec![boxed_ty.clone()];

    let call = ast::Call {
        func: ast::FunId::Assumed(aid),
        region_args,
        type_args,
        const_generic_args,
        args,
        dest,
    };
    Ok(ast::RawTerminator::Call { call, target })
}

/// Translate `core::ops::index::{Index,IndexMut}::{index,index_mut}`
/// applied on `Vec`. We need a custom function because it is a trait.
fn translate_vec_index(
    aid: ast::AssumedFunId,
    region_args: Vec<ty::ErasedRegion>,
    type_args: Vec<ty::ETy>,
    const_generic_args: Vec<ty::ConstGeneric>,
    args: Vec<e::Operand>,
    dest: e::Place,
    target: ast::BlockId::Id,
) -> Result<ast::RawTerminator> {
    // Check the arguments
    assert!(region_args.is_empty());
    assert!(type_args.len() == 1);
    assert!(args.len() == 2);

    // For now we only support index on vectors
    // Retrieve the boxed value
    let arg_ty = type_args.get(0).unwrap(); // should be `Vec<...>`
    let arg_ty = match arg_ty.as_vec() {
        Option::Some(ty) => ty,
        Option::None => {
            panic!(
            "Index/IndexMut trait applied with parameter {:?} while it is only supported on Vec<T> values",
            arg_ty
        );
        }
    };

    let type_args = vec![arg_ty.clone()];
    let call = ast::Call {
        func: ast::FunId::Assumed(aid),
        region_args,
        type_args,
        const_generic_args,
        args,
        dest,
    };
    Ok(ast::RawTerminator::Call { call, target })
}

/// Small utility
pub(crate) fn check_impl_item(impl_item: &rustc_hir::Impl<'_>) {
    // TODO: make proper error messages
    use rustc_hir::{Constness, Defaultness, ImplPolarity, Unsafety};
    assert!(impl_item.unsafety == Unsafety::Normal);
    // About polarity:
    // [https://doc.rust-lang.org/beta/unstable-book/language-features/negative-impls.html]
    // Not sure about what I should do about it. Should I do anything, actually?
    // This seems useful to enforce some discipline on the user-side, but not
    // necessary for analysis purposes.
    assert!(impl_item.polarity == ImplPolarity::Positive);
    // Note sure what this is about
    assert!(impl_item.defaultness == Defaultness::Final);
    // Note sure what this is about
    assert!(impl_item.constness == Constness::NotConst);
    assert!(impl_item.of_trait.is_none()); // We don't support traits for now
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Translate a function's local variables by adding them in the environment.
    fn translate_body_locals(&mut self, body: &hax::MirBody<()>) -> Result<()> {
        // Translate the parameters
        for (index, var) in body.local_decls.raw.iter().enumerate() {
            trace!("Translating local of index {} and type {:?}", index, var.ty);

            // Find the name of the variable
            let span = var.source_info.span;
            let name: Option<String> = var.name.clone();

            // Translate the type
            let ty = self.translate_ety(&var.ty)?;

            // Add the variable to the environment
            self.push_var(index, ty, name);
        }

        Ok(())
    }

    /// Translate an expression's body (either a function or a global).
    ///
    /// The local variables should already have been translated and inserted in
    /// the context.
    fn translate_transparent_expression_body(&mut self, body: &hax::MirBody<()>) -> Result<()> {
        trace!();

        let id = self.translate_basic_block(body, rustc_index::Idx::new(START_BLOCK.as_usize()))?;
        assert!(id == ast::START_BLOCK_ID);

        Ok(())
    }

    fn translate_basic_block(
        &mut self,
        body: &hax::MirBody<()>,
        block_id: hax::BasicBlock,
    ) -> Result<ast::BlockId::Id> {
        // Check if the block has already been translated
        if let Some(id) = self.blocks_map.get(&block_id) {
            return Ok(*id);
        }
        let nid = self.fresh_block_id(block_id);

        // Retrieve the block data
        let block = body.basic_blocks.get(block_id).unwrap();

        // Translate the statements
        let mut statements = Vec::new();
        for statement in &block.statements {
            trace!("statement: {:?}", statement);

            // Some statements might be ignored, hence the optional returned value
            let opt_statement = self.translate_statement(body, statement)?;
            if let Some(statement) = opt_statement {
                statements.push(statement)
            }
        }

        // Translate the terminator
        let terminator = block.terminator.unwrap();
        let terminator = self.translate_terminator(body, &terminator)?;

        // Insert the block in the translated blocks
        let block = ast::BlockData {
            statements,
            terminator,
        };

        self.push_block(nid, block);

        Ok(nid)
    }

    /// Translate a place and return its type
    fn translate_place_with_type(&mut self, place: &hax::Place) -> (e::Place, ty::ETy) {
        let (var_id, projection, ty) = self.translate_projection(place);
        (e::Place { var_id, projection }, ty)
    }

    /// Translate a place
    fn translate_place(&mut self, place: &hax::Place) -> e::Place {
        self.translate_place_with_type(place).0
    }

    /// Translate a place - TODO: rename
    /// TODO: Hax represents places in a different manner than MIR. We should
    /// update our representation of places to match the Hax representation.
    fn translate_projection(
        &mut self,
        place: &hax::Place,
    ) -> (v::VarId::Id, e::Projection, ty::ETy) {
        use hax::PlaceKind;
        let current_ty = self.translate_ety(&place.ty).unwrap();
        match place.kind {
            PlaceKind::Local(local) => {
                let var_id = self.get_local(&local).unwrap();
                (var_id, Vec::new(), current_ty)
            }
            PlaceKind::Projection { place, kind } => {
                let (var_id, mut projection, projected_ty) = self.translate_projection(&*place);
                use hax::ProjectionElem;
                match kind {
                    ProjectionElem::Deref => {
                        // We use the type to disambiguate
                        match current_ty {
                            ty::Ty::Ref(_, ty, _) => {
                                projection.push(e::ProjectionElem::Deref);
                            }
                            ty::Ty::Adt(
                                ty::TypeId::Assumed(ty::AssumedTy::Box),
                                regions,
                                tys,
                                cgs,
                            ) => {
                                // This case only happens in some MIR levels
                                assert!(!boxes_are_desugared(self.t_ctx.mir_level));
                                assert!(regions.is_empty());
                                assert!(tys.len() == 1);
                                assert!(cgs.is_empty());
                                projection.push(e::ProjectionElem::DerefBox);
                            }
                            ty::Ty::RawPtr(ty, _) => {
                                projection.push(e::ProjectionElem::DerefRawPtr);
                            }
                            _ => {
                                unreachable!(
                                    "\n- place.kind: {:?}\n- current_ty: {:?}",
                                    place.kind, current_ty
                                );
                            }
                        }
                    }
                    ProjectionElem::Field(field_kind) => {
                        use hax::ProjectionElemFieldKind::*;
                        let proj_elem = match field_kind {
                            Tuple(id) => {
                                let (_, _, tys, _) = current_ty.as_adt();
                                let field_id = translate_field_id(id);
                                let proj_kind = e::FieldProjKind::Tuple(tys.len());
                                e::ProjectionElem::Field(proj_kind, field_id)
                            }
                            Adt {
                                typ,
                                variant,
                                index,
                            } => {
                                let field_id = translate_field_id(index);
                                let variant_id = variant.map(|vid| translate_variant_id(vid));
                                match current_ty {
                                    ty::Ty::Adt(ty::TypeId::Adt(type_id), ..) => {
                                        let proj_kind = e::FieldProjKind::Adt(type_id, variant_id);
                                        e::ProjectionElem::Field(proj_kind, field_id)
                                    }
                                    ty::Ty::Adt(ty::TypeId::Tuple, regions, tys, cgs) => {
                                        assert!(regions.is_empty());
                                        assert!(variant.is_none());
                                        assert!(cgs.is_empty());
                                        let proj_kind = e::FieldProjKind::Tuple(tys.len());

                                        e::ProjectionElem::Field(proj_kind, field_id)
                                    }
                                    ty::Ty::Adt(
                                        ty::TypeId::Assumed(ty::AssumedTy::Option),
                                        regions,
                                        tys,
                                        cgs,
                                    ) => {
                                        assert!(regions.is_empty());
                                        assert!(tys.len() == 1);
                                        assert!(cgs.is_empty());
                                        assert!(field_id == ty::FieldId::ZERO);

                                        let variant_id = variant_id.unwrap();
                                        assert!(variant_id == assumed::OPTION_SOME_VARIANT_ID);
                                        let proj_kind = e::FieldProjKind::Option(variant_id);
                                        e::ProjectionElem::Field(proj_kind, field_id)
                                    }
                                    ty::Ty::Adt(
                                        ty::TypeId::Assumed(ty::AssumedTy::Box),
                                        regions,
                                        tys,
                                        cgs,
                                    ) => {
                                        assert!(!boxes_are_desugared(self.t_ctx.mir_level));

                                        // Some more sanity checks
                                        assert!(regions.is_empty());
                                        assert!(tys.len() == 1);
                                        assert!(cgs.is_empty());
                                        assert!(variant_id.is_none());
                                        assert!(field_id == ty::FieldId::ZERO);

                                        e::ProjectionElem::DerefBox
                                    }
                                    _ => {
                                        unreachable!();
                                    }
                                }
                            }
                        };
                        projection.push(proj_elem);
                    }
                    ProjectionElem::Index(local) => {
                        let local = self.get_local(&local).unwrap();
                        projection.push(e::ProjectionElem::Index(local, current_ty));
                    }
                    ProjectionElem::Downcast(..) => {
                        // We view it as a nop (the information from the
                        // downcast has been propagated to the other
                        // projection elements by Hax)
                        ()
                    }
                    ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. } => {
                        // Those don't seem to occur in MIR built
                        unimplemented!()
                    }
                    ProjectionElem::OpaqueCast => {
                        // Don't know what that is
                        unimplemented!()
                    }
                };

                // Return
                (var_id, projection, projected_ty)
            }
        }
    }

    /// Translate an operand with its type
    fn translate_operand_with_type(&mut self, operand: &hax::Operand) -> (e::Operand, ty::ETy) {
        trace!();
        use hax::Operand;
        match operand {
            Operand::Copy(place) => {
                let (p, ty) = self.translate_place_with_type(place);
                (e::Operand::Copy(p), ty)
            }
            Operand::Move(place) => {
                let (p, ty) = self.translate_place_with_type(place);
                (e::Operand::Move(p), ty)
            }
            Operand::Constant(constant) => {
                let (ty, constant) = self.translate_constant_to_operand_constant_value(constant);
                (e::Operand::Const(ty.clone(), constant), ty)
            }
        }
    }

    /// Translate an operand
    fn translate_operand(&mut self, operand: &hax::Operand) -> e::Operand {
        trace!();
        self.translate_operand_with_type(operand).0
    }

    /// Translate an operand which should be `move b.0` where `b` is a box (such
    /// operands are sometimes introduced here and there).
    /// This is a degenerate case where we can't use
    /// [`translate_operand`](translate_operand) on this kind of operands because
    /// it will panic, due to the fact that we precisely track the type of the
    /// values we go through during the path exploration.
    /// We also prefer not to tweak `translate_operand` to account for this
    /// ad-hoc behaviour (which comes from the fact that we abstract boxes, while
    /// the rust compiler is too precise when manipulating those boxes, which
    /// reveals implementation details).
    fn translate_move_box_first_projector_operand(&mut self, operand: &hax::Operand) -> e::Operand {
        trace!();
        match operand {
            hax::Operand::Move(place) => {
                let place = self.translate_place(place);

                // Sanity check
                let var = self.get_var_from_id(place.var_id).unwrap();
                assert!(var.ty.is_box());

                e::Operand::Move(place)
            }
            _ => {
                unreachable!();
            }
        }
    }

    /// Translate an rvalue
    fn translate_rvalue(&mut self, rvalue: &hax::Rvalue) -> e::Rvalue {
        use hax::Rvalue;
        use std::ops::Deref;
        match rvalue {
            Rvalue::Use(operand) => e::Rvalue::Use(self.translate_operand(operand)),
            Rvalue::CopyForDeref(place) => {
                // According to the documentation, it seems to be an optimisation
                // for drop elaboration. We treat it as a regular copy.
                let place = self.translate_place(place);
                e::Rvalue::Use(e::Operand::Copy(place))
            }
            Rvalue::Repeat(operand, cnst) => {
                let c = self.translate_constant_expr_to_const_generic(cnst);
                // We are effectively desugaring the repeat in Charon, turning it into an array literal
                // where the operand is repeated `cnst` times.
                // TODO: allow having other kinds of const generics, and desugar later to a function call
                let cv = *c.as_value().as_scalar().as_usize();
                let (operand, t) = self.translate_operand_with_type(operand);
                let mut operands = Vec::with_capacity(cv as usize);
                for _ in 0..cv {
                    operands.push(operand.clone());
                }
                // We *have* to desugar here; we don't have enough context (the destination place, the
                // lifetime variable) to translate this into a built-in function call. This is why we
                // don't have a ArrayRepeat AssumedFunId.
                e::Rvalue::Aggregate(e::AggregateKind::Array(t, c), operands)
            }
            Rvalue::Ref(_region, borrow_kind, place) => {
                let place = self.translate_place(place);
                let borrow_kind = translate_borrow_kind(*borrow_kind);
                e::Rvalue::Ref(place, borrow_kind)
            }
            Rvalue::ThreadLocalRef(_) => {
                unreachable!();
            }
            Rvalue::AddressOf(_, _) => {
                unreachable!();
            }
            Rvalue::Len(place) => {
                let (place, ty) = self.translate_place_with_type(place);
                let cg = match &ty {
                    ty::Ty::Adt(
                        ty::TypeId::Assumed(aty @ (ty::AssumedTy::Array | ty::AssumedTy::Slice)),
                        _,
                        _,
                        cgs,
                    ) => {
                        if aty.is_array() {
                            Option::Some(cgs[0].clone())
                        } else {
                            Option::None
                        }
                    }
                    _ => unreachable!(),
                };
                e::Rvalue::Len(place, ty, cg)
            }
            Rvalue::Cast(cast_kind, operand, tgt_ty) => {
                trace!("Rvalue::Cast: {:?}", rvalue);
                // Put aside the pointer casts (which we don't support), I think
                // casts should only be from integers/booleans to integer/booleans.

                // Translate the target type
                let tgt_ty = self.translate_ety(tgt_ty).unwrap();

                // Translate the operand
                let (op, src_ty) = self.translate_operand_with_type(operand);

                use hax::CastKind;
                match (cast_kind, &src_ty, &tgt_ty) {
                    (CastKind::IntToInt, _, _) => {
                        // We only support source and target types for integers
                        let tgt_ty = *tgt_ty.as_literal().as_integer();
                        let src_ty = *src_ty.as_literal().as_integer();

                        e::Rvalue::UnaryOp(e::UnOp::Cast(src_ty, tgt_ty), op)
                    }
                    (
                        CastKind::Pointer(hax::PointerCast::Unsize),
                        ty::Ty::Ref(_, t1, kind1),
                        ty::Ty::Ref(_, t2, kind2),
                    ) => {
                        // In MIR terminology, we go from &[T; l] to &[T] which means we
                        // effectively "unsize" the type, as `l` no longer appears in the
                        // destination type. At runtime, the converse happens: the length
                        // materializes into the fat pointer.
                        match (&**t1, &**t2) {
                            (
                                ty::Ty::Adt(ty::TypeId::Assumed(ty::AssumedTy::Array), _, tys, cgs),
                                ty::Ty::Adt(ty::TypeId::Assumed(ty::AssumedTy::Slice), _, tys1, _),
                            ) => {
                                assert!(tys.len() == 1 && cgs.len() == 1);
                                assert!(tys[0] == tys1[0]);
                                assert!(kind1 == kind2);
                                e::Rvalue::UnaryOp(
                                    e::UnOp::ArrayToSlice(*kind1, tys[0].clone(), cgs[0].clone()),
                                    op,
                                )
                            }
                            _ => {
                                panic!(
                                    "Unsupported cast: {:?}, src={:?}, dst={:?}",
                                    rvalue, src_ty, tgt_ty
                                )
                            }
                        }
                    }
                    _ => {
                        panic!(
                            "Unsupported cast: {:?}, src={:?}, dst={:?}",
                            rvalue, src_ty, tgt_ty
                        )
                    }
                }
            }
            Rvalue::BinaryOp(binop, operands) | Rvalue::CheckedBinaryOp(binop, operands) => {
                // We merge checked and unchecked binary operations
                let (left, right) = operands.deref();
                e::Rvalue::BinaryOp(
                    translate_binaryop_kind(*binop),
                    self.translate_operand(left),
                    self.translate_operand(right),
                )
            }
            Rvalue::NullaryOp(nullop, _ty) => {
                trace!("NullOp: {:?}", nullop);
                // Nullary operations are very low-level and shouldn't be necessary
                // unless one needs to write unsafe code.
                unreachable!();
            }
            Rvalue::UnaryOp(unop, operand) => e::Rvalue::UnaryOp(
                translate_unaryop_kind(*unop),
                self.translate_operand(operand),
            ),
            Rvalue::Discriminant(place) => e::Rvalue::Discriminant(self.translate_place(place)),
            Rvalue::Aggregate(aggregate_kind, operands) => {
                // It seems this instruction is not present in certain passes:
                // for example, it seems it is not used in optimized MIR, where
                // ADT initialization is split into several instructions, for
                // instance:
                // ```
                // p = Pair { x:xv, y:yv };
                // ```
                // Might become:
                // ```
                // p.x = x;
                // p.y = yv;
                // ```
                //
                // Our semantics is designed to handle both cases (aggregated and
                // non-aggregated initialization).

                // First translate the operands
                let operands_t: Vec<e::Operand> = operands
                    .raw
                    .iter()
                    .map(|op| self.translate_operand(op))
                    .collect();

                use hax::AggregateKind;
                match aggregate_kind.deref() {
                    AggregateKind::Array(ty) => {
                        let t_ty = self.translate_ety(&ty).unwrap();
                        let cg = ty::ConstGeneric::Value(Literal::Scalar(ScalarValue::Usize(
                            operands_t.len() as u64,
                        )));
                        e::Rvalue::Aggregate(e::AggregateKind::Array(t_ty, cg), operands_t)
                    }
                    AggregateKind::Tuple => {
                        e::Rvalue::Aggregate(e::AggregateKind::Tuple, operands_t)
                    }
                    AggregateKind::Adt(
                        adt_id,
                        variant_idx,
                        kind,
                        substs,
                        user_annotation,
                        field_index,
                    ) => {
                        trace!("{:?}", rvalue);

                        // Not sure what those two parameters are used for, so
                        // panicking if they are not none (to catch a use case).
                        // I'm not even sure that "field_index" is a proper name:
                        // the documentation seems outdated (it says the 4th parameter
                        // is a field index, while it makes more sense for it to be
                        // the 5th, and I don't know how I should use it anyway).
                        assert!(user_annotation.is_none());
                        assert!(field_index.is_none());

                        // Translate the substitution
                        let (region_params, mut type_params, cg_params) = self
                            .translate_subst_generic_args_in_body(None, substs)
                            .unwrap();

                        let rust_id = adt_id.rust_def_id.unwrap();
                        if rust_id.is_local() {
                            assert!(!self.t_ctx.id_is_opaque(rust_id));

                            // Local ADT: translate the id
                            let id_t = self.translate_type_decl_id(rust_id);

                            use hax::AdtKind;
                            let variant_id = match kind {
                                AdtKind::Struct => Option::None,
                                AdtKind::Enum => {
                                    let variant_id = translate_variant_id(*variant_idx);
                                    Some(variant_id)
                                }
                                AdtKind::Union => {
                                    unimplemented!();
                                }
                            };

                            let akind = e::AggregateKind::Adt(
                                id_t,
                                variant_id,
                                region_params,
                                type_params,
                                cg_params,
                            );

                            e::Rvalue::Aggregate(akind, operands_t)
                        } else {
                            // External ADT.
                            // Can be `Option`
                            // TODO: treat all external ADTs in a consistant manner.
                            // For instance, we can access the variants of any external
                            // enumeration marked as `public`.
                            let name = def_id_to_name(adt_id);
                            if name.equals_ref_name(&assumed::OPTION_NAME) {
                                // Sanity checks
                                assert!(region_params.is_empty());
                                assert!(type_params.len() == 1);

                                // Find the variant
                                let variant_id = translate_variant_id(*variant_idx);
                                if variant_id == assumed::OPTION_NONE_VARIANT_ID {
                                    assert!(operands_t.is_empty());
                                } else if variant_id == assumed::OPTION_SOME_VARIANT_ID {
                                    assert!(operands_t.len() == 1);
                                } else {
                                    unreachable!();
                                }

                                let akind = e::AggregateKind::Option(
                                    variant_id,
                                    type_params.pop().unwrap(),
                                );

                                e::Rvalue::Aggregate(akind, operands_t)
                            } else if name.equals_ref_name(&assumed::RANGE_NAME) {
                                // Sanity checks
                                assert!(region_params.is_empty());
                                // Ranges are parametric over the type of indices
                                assert!(type_params.len() == 1);
                                e::Rvalue::Aggregate(
                                    e::AggregateKind::Range(type_params.pop().unwrap()),
                                    operands_t,
                                )
                            } else {
                                panic!("Unsupported ADT: {}", name);
                            }
                        }
                    }
                    AggregateKind::Closure(_def_id, _subst) => {
                        unimplemented!();
                    }
                    AggregateKind::Generator(_def_id, _subst, _movability) => {
                        unimplemented!();
                    }
                }
            }
            Rvalue::ShallowInitBox(_, _) => {
                unimplemented!();
            }
        }
    }

    /// Translate a statement
    ///
    /// We return an option, because we ignore some statements (`Nop`, `StorageLive`...)
    fn translate_statement(
        &mut self,
        body: &hax::MirBody<()>,
        statement: &hax::Statement,
    ) -> Result<Option<ast::Statement>> {
        trace!("About to translate statement (MIR) {:?}", statement);

        use std::ops::Deref;

        use hax::StatementKind;
        let t_statement: Option<ast::RawStatement> = match &*statement.kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = assign.deref();
                let t_place = self.translate_place(place);
                let t_rvalue = self.translate_rvalue(rvalue);

                Some(ast::RawStatement::Assign(t_place, t_rvalue))
            }
            StatementKind::FakeRead(info) => {
                let (_read_cause, place) = info.deref();
                let t_place = self.translate_place(place);

                Some(ast::RawStatement::FakeRead(t_place))
            }
            StatementKind::PlaceMention(place) => {
                // Simply accesses a place. Introduced for instance in place
                // of `let _ = ...`. We desugar it to a fake read.
                let t_place = self.translate_place(place);

                Some(ast::RawStatement::FakeRead(t_place))
            }
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                let t_place = self.translate_place(place);
                let variant_id = translate_variant_id(*variant_index);
                Some(ast::RawStatement::SetDiscriminant(t_place, variant_id))
            }
            StatementKind::StorageLive(_) => {
                // We ignore StorageLive
                None
            }
            StatementKind::StorageDead(local) => {
                let var_id = self.get_local(local).unwrap();
                Some(ast::RawStatement::StorageDead(var_id))
            }
            StatementKind::Retag(_, _) => {
                // This is for the stacked borrows
                trace!("retag");
                None
            }
            StatementKind::AscribeUserType(_, _) => {
                trace!("AscribedUserType");
                // We ignore those: they are just used by the type checker.
                // Note that this instruction is used only in certain passes
                // (it is not present in optimized MIR for instance).
                None
            }
            StatementKind::Coverage(_) => {
                unimplemented!();
            }
            StatementKind::Nop => {
                // We ignore this statement
                None
            }
            StatementKind::Deinit(place) => {
                let t_place = self.translate_place(place);
                Some(ast::RawStatement::Deinit(t_place))
            }
            StatementKind::Intrinsic(_) => {
                unimplemented!();
            }
            StatementKind::ConstEvalCounter => {
                // See the doc: only used in the interpreter, to check that
                // const code doesn't run for too long or even indefinitely.
                // We consider it as a no-op.
                None
            }
        };

        // Add the meta information
        match t_statement {
            None => Ok(None),
            Some(t_statement) => {
                let meta = self
                    .t_ctx
                    .translate_meta_from_source_info(&body.source_scopes, statement.source_info);

                Ok(Some(ast::Statement::new(meta, t_statement)))
            }
        }
    }

    /// Translate a terminator
    fn translate_terminator(
        &mut self,
        body: &hax::MirBody<()>,
        terminator: &hax::Terminator,
    ) -> Result<ast::Terminator> {
        trace!("About to translate terminator (MIR) {:?}", terminator);

        // Compute the meta information beforehand (we might need it to introduce
        // intermediate statements - we desugar some terminators)
        let meta = self
            .t_ctx
            .translate_meta_from_source_info(&body.source_scopes, terminator.source_info);

        // Translate the terminator
        use hax::TerminatorKind;
        let t_terminator: ast::RawTerminator = match &terminator.kind {
            TerminatorKind::Goto { target } => {
                let target = self.translate_basic_block(body, *target)?;
                ast::RawTerminator::Goto { target }
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                // Translate the operand which gives the discriminant
                let (discr, discr_ty) = self.translate_operand_with_type(discr);

                // Translate the switch targets
                let targets = self.translate_switch_targets(body, &discr_ty, targets);

                ast::RawTerminator::Switch { discr, targets }
            }
            TerminatorKind::Resume => {
                // This is used to correctly unwind. We shouldn't get there: if
                // we panic, the state gets stuck.
                unreachable!();
            }
            TerminatorKind::Return => ast::RawTerminator::Return,
            TerminatorKind::Unreachable => ast::RawTerminator::Unreachable,
            TerminatorKind::Terminate => unimplemented!(),
            TerminatorKind::Drop {
                place,
                target,
                unwind: _, // We consider that panic is an error, and don't model unwinding
                replace: _,
            } => ast::RawTerminator::Drop {
                place: self.translate_place(place),
                target: self.translate_basic_block(body, *target)?,
            },
            TerminatorKind::Call {
                fun_id,
                substs,
                args,
                destination,
                target,
                unwind: _, // We consider that panic is an error, and don't model unwinding
                from_hir_call: _,
                fn_span: _,
            } => {
                trace!("Call: func: {:?}", fun_id.rust_def_id);
                self.translate_function_call(body, fun_id, substs, args, destination, target)?
            }
            TerminatorKind::Assert {
                cond,
                expected,
                msg: _,
                target,
                unwind: _, // We consider that panic is an error, and don't model unwinding
            } => {
                let cond = self.translate_operand(cond);
                let target = self.translate_basic_block(body, *target)?;
                ast::RawTerminator::Assert {
                    cond,
                    expected: *expected,
                    target,
                }
            }
            TerminatorKind::Yield {
                value: _,
                resume: _,
                resume_arg: _,
                drop: _,
            } => {
                unimplemented!();
            }
            TerminatorKind::GeneratorDrop => {
                unimplemented!();
            }
            TerminatorKind::FalseEdge {
                real_target,
                imaginary_target,
            } => {
                trace!(
                    "False edge:\n- real target ({:?}):\n{:?}\n- imaginary target ({:?}):\n{:?}",
                    real_target,
                    body.basic_blocks.get(*real_target).unwrap(),
                    imaginary_target,
                    body.basic_blocks.get(*imaginary_target).unwrap(),
                );

                // False edges are used to make the borrow checker a bit conservative.
                // We translate them as Gotos.
                // Also note that they are used in some passes, and not in some others
                // (they are present in mir_promoted, but not mir_optimized).
                let target = self.translate_basic_block(body, *real_target)?;
                ast::RawTerminator::Goto { target }
            }
            TerminatorKind::FalseUnwind {
                real_target,
                unwind: _,
            } => {
                // We consider this to be a goto
                let target = self.translate_basic_block(body, *real_target)?;
                ast::RawTerminator::Goto { target }
            }
            TerminatorKind::InlineAsm { .. } => {
                // This case should have been eliminated during the registration phase
                unreachable!();
            }
        };

        // Add the meta information
        Ok(ast::Terminator::new(meta, t_terminator))
    }

    /// Translate switch targets
    fn translate_switch_targets(
        &mut self,
        body: &hax::MirBody<()>,
        switch_ty: &ty::ETy,
        targets: &hax::SwitchTargets,
    ) -> ast::SwitchTargets {
        trace!("targets: {:?}", targets);
        use hax::SwitchTargets;
        match targets {
            SwitchTargets::If(if_block, then_block) => {
                let if_block = self.translate_basic_block(body, *if_block).unwrap();
                let then_block = self.translate_basic_block(body, *then_block).unwrap();
                ast::SwitchTargets::If(if_block, then_block)
            }
            SwitchTargets::SwitchInt(_, targets_map, otherwise) => {
                let int_ty = *switch_ty.as_literal().as_integer();
                let targets_map = targets_map
                    .iter()
                    .map(|(v, tgt)| {
                        let v = v::ScalarValue::from_le_bytes(int_ty, v.data_le_bytes);
                        let tgt = self.translate_basic_block(body, *tgt).unwrap();
                        (v, tgt)
                    })
                    .collect();
                let otherwise = self.translate_basic_block(body, *otherwise).unwrap();
                ast::SwitchTargets::SwitchInt(int_ty, targets_map, otherwise)
            }
        }
    }

    /// Translate a function call statement.
    /// Note that `body` is the body of the function being translated, not of the
    /// function referenced in the function call: we need it in order to translate
    /// the blocks we go to after the function call returns.
    fn translate_function_call(
        &mut self,
        body: &hax::MirBody<()>,
        def_id: &hax::DefId,
        substs: &Vec<hax::GenericArg>,
        args: &Vec<hax::Operand>,
        destination: &hax::Place,
        target: &Option<hax::BasicBlock>,
    ) -> Result<ast::RawTerminator> {
        trace!();
        let rust_id = def_id.rust_def_id.unwrap();

        // Translate the function operand - should be a constant: we don't
        // support closures for now
        trace!("func: {:?}", rust_id);

        let tcx = self.t_ctx.tcx;

        // Translate the name to check if is is `core::panicking::panic`
        // TODO: replace
        let name = def_id_to_name(def_id);
        let is_local = rust_id.is_local();

        // If the call is `panic!`, then the target is `None`.
        // I don't know in which other cases it can be `None`.
        if name.equals_ref_name(&assumed::PANIC_NAME)
            || name.equals_ref_name(&assumed::BEGIN_PANIC_NAME)
        {
            assert!(!is_local);
            assert!(target.is_none());

            // We ignore the arguments
            Ok(ast::RawTerminator::Panic)
        } else {
            assert!(target.is_some());
            let next_block = target.unwrap();

            // Translate the target
            let lval = self.translate_place(destination);
            let next_block = self.translate_basic_block(body, next_block)?;

            // There is something annoying: when going to MIR, the rust compiler
            // sometimes introduces very low-level functions, which we need to
            // catch early - in particular, before we start translating types and
            // arguments, because we won't be able to translate some of them.
            if name.equals_ref_name(&assumed::BOX_FREE_NAME) {
                assert!(!is_local);

                // This deallocates a box.
                // It should have two type parameters:
                // - the type of the boxed value
                // - the type of a global allocator (which we ignore)
                // The arguments should be of the form:
                // - `move b.0` (the allocated value)
                // - `move b.1` (the global allocated)
                // where b is of type `Box` (boxes are pairs actually)
                // We replace that with: `move b`
                assert!(substs.len() == 2);
                assert!(args.len() == 2);

                // Translate the type parameter
                let t_ty = if let hax::GenericArg::Type(ty) = substs.get(0).unwrap() {
                    self.translate_ety(ty)?
                } else {
                    unreachable!()
                };

                // Translate the first argument - note that we use a special
                // function to translate it: the operand should be of the form:
                // `move b.0`, and if it is the case it will return `move b`
                let arg = &args[0];
                let t_arg = self.translate_move_box_first_projector_operand(arg);

                // Return
                let call = ast::Call {
                    func: ast::FunId::Assumed(ast::AssumedFunId::BoxFree),
                    region_args: vec![],
                    type_args: vec![t_ty],
                    const_generic_args: vec![],
                    args: vec![t_arg],
                    dest: lval,
                };
                Ok(ast::RawTerminator::Call {
                    call,
                    target: next_block,
                })
            } else {
                // Retrieve the lists of used parameters, in case of non-local
                // definitions
                let (used_type_args, used_args) = if is_local {
                    (Option::None, Option::None)
                } else {
                    match assumed::function_to_info(&name) {
                        Option::None => (Option::None, Option::None),
                        Option::Some(used) => (
                            Option::Some(used.used_type_params),
                            Option::Some(used.used_args),
                        ),
                    }
                };

                // Translate the type parameters
                let (region_args, type_args, const_generic_args) =
                    self.translate_subst_generic_args_in_body(used_type_args, substs)?;

                // Translate the arguments
                let args = self.translate_arguments(used_args, args);

                // Check if the function is considered primitive: primitive
                // functions benefit from special treatment.
                let is_prim = if is_local {
                    false
                } else {
                    assumed::get_fun_id_from_name(&name, &type_args).is_some()
                };

                if !is_prim {
                    // Retrieve the def id
                    let def_id = self.translate_fun_decl_id(rust_id);

                    let func = ast::FunId::Regular(def_id);
                    let call = ast::Call {
                        func,
                        region_args,
                        type_args,
                        const_generic_args,
                        args,
                        dest: lval,
                    };

                    Ok(ast::RawTerminator::Call {
                        call,
                        target: next_block,
                    })
                } else {
                    // Primitive function.
                    //
                    // Note that there are subtleties with regards to the way types parameters
                    // are translated, because some functions are actually traits, where the
                    // types are used for the resolution. For instance, the following:
                    // `core::ops::deref::Deref::<alloc::boxed::Box<T>>::deref`
                    // is translated to:
                    // `box_deref<T>`
                    // (the type parameter is not `Box<T>` but `T`).
                    translate_primitive_function_call(
                        tcx,
                        def_id,
                        region_args,
                        type_args,
                        const_generic_args,
                        args,
                        lval,
                        next_block,
                    )
                }
            }
        }
    }

    /// Translate a parameter substitution used inside a function body.
    ///
    /// Note that the regions parameters are expected to have been erased.
    fn translate_subst_generic_args_in_body(
        &mut self,
        used_args: Option<Vec<bool>>,
        substs: &Vec<hax::GenericArg>,
    ) -> Result<(Vec<ty::ErasedRegion>, Vec<ty::ETy>, Vec<ty::ConstGeneric>)> {
        let substs: Vec<&hax::GenericArg> = match used_args {
            Option::None => substs.into_iter().collect(),
            Option::Some(used_args) => {
                assert!(substs.len() == used_args.len());
                substs
                    .into_iter()
                    .zip(used_args.into_iter())
                    .filter_map(|(param, used)| if used { Some(param) } else { None })
                    .collect()
            }
        };

        let mut t_args_regions = Vec::new();
        let mut t_args_tys = Vec::new();
        let mut t_args_cgs = Vec::new();
        for param in substs.into_iter() {
            use hax::GenericArg;
            match param {
                GenericArg::Type(param_ty) => {
                    // Simply translate the type
                    let t_param_ty = self.translate_ety(&param_ty)?;
                    t_args_tys.push(t_param_ty);
                }
                GenericArg::Lifetime(region) => {
                    t_args_regions.push(translate_erased_region(*region));
                }
                GenericArg::Const(c) => {
                    let t_cg = self.translate_constant_expr_to_const_generic(c);
                    t_args_cgs.push(t_cg);
                }
            }
        }

        Ok((t_args_regions, t_args_tys, t_args_cgs))
    }

    /// Evaluate function arguments in a context, and return the list of computed
    /// values.
    fn translate_arguments(
        &mut self,
        used_args: Option<Vec<bool>>,
        args: &Vec<hax::Operand>,
    ) -> Vec<e::Operand> {
        let args: Vec<&hax::Operand> = match used_args {
            Option::None => args.iter().collect(),
            Option::Some(used_args) => {
                assert!(args.len() == used_args.len());
                args.iter()
                    .zip(used_args.into_iter())
                    .filter_map(|(param, used)| if used { Some(param) } else { None })
                    .collect()
            }
        };

        let mut t_args: Vec<e::Operand> = Vec::new();
        for arg in args {
            // There should only be moved arguments, or constants
            match arg {
                hax::Operand::Move(_) | hax::Operand::Constant(_) => {
                    // OK
                }
                hax::Operand::Copy(_) => {
                    unreachable!();
                }
            }

            // Translate
            let op = self.translate_operand(arg);
            t_args.push(op);
        }

        t_args
    }

    fn translate_body(mut self, local_id: LocalDefId, arg_count: usize) -> Result<ast::ExprBody> {
        let tcx = self.t_ctx.tcx;

        // Retrive the body
        let body = get_mir_for_def_id_and_level(tcx, local_id, self.t_ctx.mir_level);

        // TODO: factor this out
        let state = hax::state::State::new_from_mir(
            tcx,
            &hax::options::Options {
                inline_macro_calls: Vec::new(),
            },
            // TODO: do we really have to clone this?
            body.clone(),
        );
        // Translate
        let body: hax::MirBody<()> = body.sinto(&state);

        // Compute the meta information
        let meta = self.translate_meta_from_hax_span(body.span);

        // Initialize the local variables
        trace!("Translating the body locals");
        self.translate_body_locals(&body)?;

        // Translate the expression body
        trace!("Translating the expression body");
        self.translate_transparent_expression_body(&body)?;

        // We need to convert the blocks map to an index vector
        // We clone things while we could move them...
        let mut blocks = ast::BlockId::Vector::new();
        for (id, block) in self.blocks {
            use crate::id_vector::ToUsize;
            // Sanity check to make sure we don't mess with the indices
            assert!(id.to_usize() == blocks.len());
            blocks.push_back(block);
        }

        // Create the body
        Ok(ast::ExprBody {
            meta,
            arg_count,
            locals: self.vars,
            body: blocks,
        })
    }
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// Translate a function's signature, and initialize a body translation context
    /// at the same time - the function signature gives us the list of region and
    /// type parameters, that we put in the translation context.
    fn translate_function_signature<'ctx1>(
        &'ctx1 mut self,
        def_id: DefId,
    ) -> (BodyTransCtx<'tcx, 'ctx1, 'ctx>, ast::FunSig) {
        let tcx = self.tcx;

        // TODO: factor this out
        let state = hax::state::State::new(
            self.tcx,
            &hax::options::Options {
                inline_macro_calls: Vec::new(),
            },
        );

        // Retrieve the function signature, which includes the lifetimes
        let signature = tcx.fn_sig(def_id).subst_identity();

        // Instantiate the signature's bound region variables (the signature
        // is wrapped in a [`Binder`](rustc_middle::ty::Binder). This is inspired by
        // [`liberate_late_bound_regions`](TyCtx::liberate_late_bound_regions).
        // The rationale is as follows:
        // - it seems liberate_late_bound_regions is a proper way of retrieving
        //   a signature where all the bound variables have been replaced with
        //   free variables, so that we can study it easily (without having, for
        //   instance, to deal with DeBruijn indices)
        // - my understanding of why it is enough to bind late-bound regions: the
        //   early bound regions are not bound here (they are free), because
        //   they reference regions introduced by the `impl` block (if this definition
        //   is defined in an `impl` block - otherwise there are no early bound variables)
        //   while the late bound regions are introduced by the function itself.
        //   For example, in:
        //   ```
        //   impl<'a> Foo<'a> {
        //       fn bar<'b>(...) -> ... { ... }
        //   }
        //   ```
        //   `'a` is early-bound while `'b` is late-bound.
        // - we can't just use `liberate_late_bound_regions`, because we want to know
        //   in which *order* the regions were bound - it is mostly a matter of stability
        //   of the translation: we will have to generate one backward function per
        //   region, and we need to know in which order to introduce those backward
        //   functions.
        //   Actually, `liberate_late_bound_regions` returns a b-tree: maybe the
        //   order between the bound regions is such that when iterating over the
        //   keys of this tree, we iterator over the bound regions in the order in
        //   which they are bound. As we are not too sure about that, we prefer
        //   reimplementing our own function, which is quite simple.

        // We need a body translation context to keep track of all the variables
        let mut bt_ctx = BodyTransCtx::new(def_id, self);

        // **Sanity checks on the HIR**
        generics::check_function_generics(tcx, def_id);

        // Start by translating the "normal" substitution (which lists the function's
        // parameters). As written above, this substitution contains all the type
        // variables, and the early-bound regions, but not the late-bound ones.
        // TODO: we do something similar in `translate_function`
        let fun_type = tcx.type_of(def_id).subst_identity();
        let substs = match fun_type.kind() {
            TyKind::FnDef(_def_id, substs_ref) => substs_ref,
            _ => {
                unreachable!()
            }
        };
        let substs = substs.sinto(&state);

        for param in substs {
            use hax::GenericArg;
            match param {
                GenericArg::Type(param_ty) => {
                    // This type should be a param type
                    match param_ty {
                        hax::Ty::Param(param_ty) => {
                            bt_ctx.push_type_var(param_ty.index, param_ty.name);
                        }
                        _ => {
                            unreachable!();
                        }
                    }
                }
                GenericArg::Lifetime(region) => {
                    let name = translate_region_name(&region);
                    bt_ctx.push_region(region, name);
                }
                GenericArg::Const(c) => {
                    // The type should be primitive, meaning it shouldn't contain
                    // variables, etc. (we could use an empty context).
                    let ty = bt_ctx.translate_ety(&c.ty).unwrap();
                    let ty = ty.to_literal();
                    match *c.contents {
                        hax::ConstantExprKind::ConstRef { id: cp } => {
                            bt_ctx.push_const_generic_var(cp.index, ty, cp.name);
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }

        // Instantiate the regions bound in the signature, and generate a mapping
        // while doing so (the mapping uses a linked hash map so that we remember
        // in which order we introduced the regions).
        // Note that replace_late_bound_regions` returns a map from bound regions to
        // regions, but it is unclear whether this map preserves the order in which
        // the regions were introduced (the map is a BTreeMap, so I guess it depends
        // on how the the bound variables were numbered) and it doesn't cost us
        // much to create this mapping ourselves.
        let (signature, late_bound_regions) =
            generics::replace_late_bound_regions(tcx, signature, def_id);

        // Introduce identifiers and translated regions for the late-bound regions
        for (_, region) in late_bound_regions.into_iter() {
            let name = translate_region_name(&region);
            bt_ctx.push_region(region, name);
        }

        trace!(
            "# Early and late bound regions:\n{}",
            iterator_to_string(
                &|x: &ty::RegionVar| x.to_string(),
                bt_ctx.region_vars.iter()
            )
        );
        trace!(
            "# Type variables:\n{}",
            iterator_to_string(&|x: &ty::TypeVar| x.to_string(), bt_ctx.type_vars.iter())
        );

        // Now that we instantiated all the binders and introduced identifiers for
        // all the variables, we can translate the function's signature.
        let inputs: Vec<ty::RTy> = Vec::from_iter(
            signature
                .inputs()
                .iter()
                .map(|ty| bt_ctx.translate_sig_ty(&(*ty).sinto(&state)).unwrap()),
        );
        let output = bt_ctx
            .translate_sig_ty(&signature.output().sinto(&state))
            .unwrap();

        trace!(
            "# Input variables types:\n{}",
            iterator_to_string(&|x| bt_ctx.format_object(x), inputs.iter())
        );
        trace!("# Output variable type:\n{}", bt_ctx.format_object(&output));

        let sig = ast::FunSig {
            region_params: bt_ctx.region_vars.clone(),
            num_early_bound_regions: late_bound_regions.len(),
            regions_hierarchy: RegionGroups::new(), // Hierarchy not yet computed
            type_params: bt_ctx.type_vars.clone(),
            const_generic_params: bt_ctx.const_generic_vars.clone(),
            inputs,
            output,
        };

        (bt_ctx, sig)
    }

    /// Translate one function.
    pub(crate) fn translate_function(&mut self, rust_id: DefId) {
        trace!("About to translate function:\n{:?}", rust_id);
        let def_id = self.translate_fun_decl_id(rust_id);
        let is_transparent = self.id_is_transparent(rust_id);

        // Compute the meta information
        let meta = self.translate_meta_from_rid(rust_id);

        // TODO: factor this out
        let state = hax::state::State::new(
            self.tcx,
            &hax::options::Options {
                inline_macro_calls: Vec::new(),
            },
        );

        // Translate the function name
        let name = def_id_to_name(&rust_id.sinto(&state));

        // Translate the function signature and initialize the body translation context
        // at the same time (the signature gives us the region and type parameters,
        // that we put in the translation context).
        trace!("Translating function signature");
        let (bt_ctx, signature) = self.translate_function_signature(rust_id);

        // Check if the type is opaque or transparent
        let is_local = rust_id.is_local();
        let body = if !is_transparent || !is_local {
            Option::None
        } else {
            Option::Some(
                bt_ctx
                    .translate_body(rust_id.expect_local(), signature.inputs.len())
                    .unwrap(),
            )
        };

        // Save the new function
        self.fun_defs.insert(
            def_id,
            ast::FunDecl {
                meta,
                def_id,
                name,
                signature,
                body,
            },
        );
    }

    /// Generate an expression body from a typed constant value.
    fn global_generate_assignment_body(
        &mut self,
        ty: ty::ETy,
        def_rid: DefId,
        val: e::OperandConstantValue,
    ) -> ast::ExprBody {
        // Compute the meta information (we use the same everywhere)
        let meta = self.translate_meta_from_rid(def_rid);

        // # Variables
        // ret : ty
        let var = ast::Var {
            index: v::VarId::ZERO,
            name: None,
            ty: ty.clone(),
        };
        // # Instructions
        // ret := const (ty, val)
        // return
        let block = ast::BlockData {
            statements: vec![ast::Statement::new(
                meta,
                ast::RawStatement::Assign(
                    e::Place::new(var.index),
                    e::Rvalue::Use(e::Operand::Const(ty, val)),
                ),
            )],
            terminator: ast::Terminator::new(meta, ast::RawTerminator::Return),
        };
        ast::ExprBody {
            meta,
            arg_count: 0,
            locals: id_vector::Vector::from(vec![var]),
            body: id_vector::Vector::from(vec![block]),
        }
    }

    /// Translate one global.
    pub(crate) fn translate_global(&mut self, rust_id: DefId) {
        trace!("About to translate global:\n{:?}", rust_id);

        let def_id = self.translate_global_decl_id(rust_id);

        // TODO: factor this out
        let state = hax::state::State::new(
            self.tcx,
            &hax::options::Options {
                inline_macro_calls: Vec::new(),
            },
        );

        // Translate the global name
        let name = def_id_to_name(&rust_id.sinto(&state));

        // Compute the meta information
        let meta = self.translate_meta_from_rid(rust_id);
        let is_transparent = self.id_is_transparent(rust_id);

        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        trace!("Translating global type");
        let mir_ty = bt_ctx.t_ctx.tcx.type_of(rust_id).subst_identity();
        let ty = bt_ctx.translate_ety(&mir_ty.sinto(&state)).unwrap();

        let body = match (rust_id.is_local(), is_transparent) {
            // It's a local and opaque global: we do not give it a body.
            (true, false) => Option::None,

            // It's a local and transparent global: we extract its body as for functions.
            (true, true) => Option::Some(bt_ctx.translate_body(rust_id.expect_local(), 0).unwrap()),

            // It is an external global.
            // The fact that it is listed among the declarations to extract means that
            // some local declaration depends on it.
            // Consequently, we try to evaluate its value.
            // If the evaluation succeeds, we generate a body.
            // If the evaluation fails, we warn about the failure and generate an
            // empty body.
            // TODO: we should keep the external globals opaque
            (false, _) => {
                let unev = rid_as_unevaluated_constant(rust_id);
                match bt_ctx.t_ctx.tcx.const_eval_resolve(
                    mir_ty::ParamEnv::empty(),
                    unev,
                    Option::None,
                ) {
                    std::result::Result::Ok(c) => {
                        // Evaluate the constant
                        let span = bt_ctx.t_ctx.tcx.def_span(rust_id);
                        let val = bt_ctx.translate_evaluated_operand_constant(mir_ty, &c, span);
                        Option::Some(bt_ctx.t_ctx.global_generate_assignment_body(
                            ty.clone(),
                            rust_id,
                            val,
                        ))
                    }
                    std::result::Result::Err(e) => {
                        warn!("Did not evaluate {:?}: {:?}", rust_id, e);
                        Option::None
                    }
                }
            }
        };

        // Save the new global
        self.global_defs.insert(
            def_id,
            ast::GlobalDecl {
                def_id,
                meta,
                name,
                ty,
                body,
            },
        );
    }
}
