//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

use std::collections::HashMap;
use std::collections::VecDeque;
use std::mem;
use std::ops::Deref;
use std::ops::DerefMut;
use std::panic;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::common::*;
use charon_lib::formatter::{Formatter, IntoFormatter};
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::ullbc_ast::*;
use hax_frontend_exporter as hax;
use itertools::Itertools;
use rustc_middle::mir;

/// A translation context for function bodies.
pub(crate) struct BodyTransCtx<'tcx, 'tctx, 'ictx> {
    /// The translation context for the item.
    pub i_ctx: &'ictx mut ItemTransCtx<'tcx, 'tctx>,

    /// The (regular) variables in the current function body.
    pub locals: Locals,
    /// The map from rust variable indices to translated variables indices.
    pub locals_map: HashMap<usize, LocalId>,
    /// The translated blocks.
    pub blocks: Vector<BlockId, BlockData>,
    /// The map from rust blocks to translated blocks.
    /// Note that when translating terminators like DropAndReplace, we might have
    /// to introduce new blocks which don't appear in the original MIR.
    pub blocks_map: HashMap<hax::BasicBlock, BlockId>,
    /// We register the blocks to translate in a stack, so as to avoid
    /// writing the translation functions as recursive functions. We do
    /// so because we had stack overflows in the past.
    pub blocks_stack: VecDeque<hax::BasicBlock>,
}

impl<'tcx, 'tctx, 'ictx> BodyTransCtx<'tcx, 'tctx, 'ictx> {
    pub(crate) fn new(i_ctx: &'ictx mut ItemTransCtx<'tcx, 'tctx>) -> Self {
        BodyTransCtx {
            i_ctx,
            locals: Default::default(),
            locals_map: Default::default(),
            blocks: Default::default(),
            blocks_map: Default::default(),
            blocks_stack: Default::default(),
        }
    }
}

impl<'tcx, 'tctx, 'ictx> Deref for BodyTransCtx<'tcx, 'tctx, 'ictx> {
    type Target = ItemTransCtx<'tcx, 'tctx>;
    fn deref(&self) -> &Self::Target {
        self.i_ctx
    }
}
impl<'tcx, 'tctx, 'ictx> DerefMut for BodyTransCtx<'tcx, 'tctx, 'ictx> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.i_ctx
    }
}

fn translate_variant_id(id: hax::VariantIdx) -> VariantId {
    VariantId::new(id)
}

fn translate_field_id(id: hax::FieldIdx) -> FieldId {
    use rustc_index::Idx;
    FieldId::new(id.index())
}

/// Translate a `BorrowKind`
fn translate_borrow_kind(borrow_kind: hax::BorrowKind) -> BorrowKind {
    match borrow_kind {
        hax::BorrowKind::Shared => BorrowKind::Shared,
        hax::BorrowKind::Mut { kind } => match kind {
            hax::MutBorrowKind::Default => BorrowKind::Mut,
            hax::MutBorrowKind::TwoPhaseBorrow => BorrowKind::TwoPhaseMut,
            hax::MutBorrowKind::ClosureCapture => BorrowKind::UniqueImmutable,
        },
        hax::BorrowKind::Fake(hax::FakeBorrowKind::Shallow) => BorrowKind::Shallow,
        // This one is used only in deref patterns.
        hax::BorrowKind::Fake(hax::FakeBorrowKind::Deep) => unimplemented!(),
    }
}

impl BodyTransCtx<'_, '_, '_> {
    pub(crate) fn translate_local(&self, local: &hax::Local) -> Option<LocalId> {
        use rustc_index::Idx;
        self.locals_map.get(&local.index()).copied()
    }

    pub(crate) fn push_var(&mut self, rid: usize, ty: Ty, name: Option<String>) {
        let local_id = self
            .locals
            .locals
            .push_with(|index| Local { index, name, ty });
        self.locals_map.insert(rid, local_id);
    }

    fn translate_binaryop_kind(&mut self, _span: Span, binop: hax::BinOp) -> Result<BinOp, Error> {
        Ok(match binop {
            hax::BinOp::BitXor => BinOp::BitXor,
            hax::BinOp::BitAnd => BinOp::BitAnd,
            hax::BinOp::BitOr => BinOp::BitOr,
            hax::BinOp::Eq => BinOp::Eq,
            hax::BinOp::Lt => BinOp::Lt,
            hax::BinOp::Le => BinOp::Le,
            hax::BinOp::Ne => BinOp::Ne,
            hax::BinOp::Ge => BinOp::Ge,
            hax::BinOp::Gt => BinOp::Gt,
            hax::BinOp::Div => BinOp::Div,
            hax::BinOp::Rem => BinOp::Rem,
            hax::BinOp::Add => BinOp::Add,
            hax::BinOp::Sub => BinOp::Sub,
            hax::BinOp::Mul => BinOp::Mul,
            hax::BinOp::AddWithOverflow => BinOp::CheckedAdd,
            hax::BinOp::SubWithOverflow => BinOp::CheckedSub,
            hax::BinOp::MulWithOverflow => BinOp::CheckedMul,
            hax::BinOp::Shl => BinOp::Shl,
            hax::BinOp::Shr => BinOp::Shr,
            hax::BinOp::Cmp => BinOp::Cmp,
            hax::BinOp::Offset => BinOp::Offset,
        })
    }

    /// Translate a function's local variables by adding them in the environment.
    fn translate_body_locals(&mut self, body: &hax::MirBody<()>) -> Result<(), Error> {
        // Translate the parameters
        for (index, var) in body.local_decls.raw.iter().enumerate() {
            trace!("Translating local of index {} and type {:?}", index, var.ty);

            // Find the name of the variable
            let name: Option<String> = var.name.clone();

            // Translate the type
            let span = self.translate_span_from_hax(&var.source_info.span);
            let ty = self.translate_ty(span, &var.ty)?;

            // Add the variable to the environment
            self.push_var(index, ty, name);
        }

        Ok(())
    }

    /// Translate a basic block id and register it, if it hasn't been done.
    fn translate_basic_block_id(&mut self, block_id: hax::BasicBlock) -> BlockId {
        match self.blocks_map.get(&block_id) {
            Some(id) => *id,
            // Generate a fresh id - this also registers the block
            None => {
                // Push to the stack of blocks awaiting translation
                self.blocks_stack.push_back(block_id);
                let id = self.blocks.reserve_slot();
                // Insert in the map
                self.blocks_map.insert(block_id, id);
                id
            }
        }
    }

    fn translate_basic_block(
        &mut self,
        body: &hax::MirBody<()>,
        block: &hax::BasicBlockData,
    ) -> Result<BlockData, Error> {
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
        let terminator = block.terminator.as_ref().unwrap();
        let terminator = self.translate_terminator(body, terminator, &mut statements)?;

        Ok(BlockData {
            statements,
            terminator,
        })
    }

    /// Translate a place
    /// TODO: Hax represents places in a different manner than MIR. We should
    /// update our representation of places to match the Hax representation.
    fn translate_place(&mut self, span: Span, place: &hax::Place) -> Result<Place, Error> {
        match &place.kind {
            hax::PlaceKind::Local(local) => {
                let var_id = self.translate_local(local).unwrap();
                Ok(self.locals.place_for_var(var_id))
            }
            hax::PlaceKind::Projection {
                place: subplace,
                kind,
            } => {
                let ty = self.translate_ty(span, &place.ty)?;
                // Compute the type of the value *before* projection - we use this
                // to disambiguate
                let subplace = self.translate_place(span, subplace)?;
                let place = match kind {
                    hax::ProjectionElem::Deref => {
                        // We use the type to disambiguate
                        match subplace.ty().kind() {
                            TyKind::Ref(_, _, _) | TyKind::RawPtr(_, _) => {}
                            TyKind::Adt(TypeId::Builtin(BuiltinTy::Box), generics) => {
                                assert!(generics.regions.is_empty());
                                assert!(generics.types.elem_count() == 1);
                                assert!(generics.const_generics.is_empty());
                            }
                            _ => {
                                unreachable!(
                                    "\n- place.kind: {:?}\n- subplace.ty(): {:?}",
                                    kind,
                                    subplace.ty()
                                )
                            }
                        }
                        subplace.project(ProjectionElem::Deref, ty)
                    }
                    hax::ProjectionElem::Field(field_kind) => {
                        use hax::ProjectionElemFieldKind::*;
                        let proj_elem = match field_kind {
                            Tuple(id) => {
                                let (_, generics) = subplace.ty().kind().as_adt().unwrap();
                                let field_id = translate_field_id(*id);
                                let proj_kind = FieldProjKind::Tuple(generics.types.elem_count());
                                ProjectionElem::Field(proj_kind, field_id)
                            }
                            Adt {
                                typ: _,
                                variant,
                                index,
                            } => {
                                let field_id = translate_field_id(*index);
                                let variant_id = variant.map(translate_variant_id);
                                match subplace.ty().kind() {
                                    TyKind::Adt(TypeId::Adt(type_id), ..) => {
                                        let proj_kind = FieldProjKind::Adt(*type_id, variant_id);
                                        ProjectionElem::Field(proj_kind, field_id)
                                    }
                                    TyKind::Adt(TypeId::Tuple, generics) => {
                                        assert!(generics.regions.is_empty());
                                        assert!(variant.is_none());
                                        assert!(generics.const_generics.is_empty());
                                        let proj_kind =
                                            FieldProjKind::Tuple(generics.types.elem_count());

                                        ProjectionElem::Field(proj_kind, field_id)
                                    }
                                    TyKind::Adt(TypeId::Builtin(BuiltinTy::Box), generics) => {
                                        // Some more sanity checks
                                        assert!(generics.regions.is_empty());
                                        assert!(generics.types.elem_count() == 1);
                                        assert!(generics.const_generics.is_empty());
                                        assert!(variant_id.is_none());
                                        assert!(field_id == FieldId::ZERO);

                                        ProjectionElem::Deref
                                    }
                                    _ => {
                                        raise_error!(self, span, "Unexpected field projection");
                                    }
                                }
                            }
                            ClosureState(index) => {
                                let field_id = translate_field_id(*index);
                                ProjectionElem::Field(FieldProjKind::ClosureState, field_id)
                            }
                        };
                        subplace.project(proj_elem, ty)
                    }
                    hax::ProjectionElem::Index(local) => {
                        let var_id = self.translate_local(local).unwrap();
                        let local = self.locals.place_for_var(var_id);
                        let offset = Operand::Copy(local);
                        subplace.project(
                            ProjectionElem::Index {
                                offset: Box::new(offset),
                                from_end: false,
                            },
                            ty,
                        )
                    }
                    hax::ProjectionElem::Downcast(..) => {
                        // We view it as a nop (the information from the
                        // downcast has been propagated to the other
                        // projection elements by Hax)
                        subplace
                    }
                    &hax::ProjectionElem::ConstantIndex {
                        offset,
                        from_end,
                        min_length: _,
                    } => {
                        let offset = Operand::Const(ScalarValue::Usize(offset).to_constant());
                        subplace.project(
                            ProjectionElem::Index {
                                offset: Box::new(offset),
                                from_end,
                            },
                            ty,
                        )
                    }
                    &hax::ProjectionElem::Subslice { from, to, from_end } => {
                        let from = Operand::Const(ScalarValue::Usize(from).to_constant());
                        let to = Operand::Const(ScalarValue::Usize(to).to_constant());
                        subplace.project(
                            ProjectionElem::Subslice {
                                from: Box::new(from),
                                to: Box::new(to),
                                from_end,
                            },
                            ty,
                        )
                    }
                    hax::ProjectionElem::OpaqueCast => {
                        // Don't know what that is
                        raise_error!(self, span, "Unexpected ProjectionElem::OpaqueCast");
                    }
                };

                // Return
                Ok(place)
            }
        }
    }

    /// Translate an operand with its type
    fn translate_operand_with_type(
        &mut self,
        span: Span,
        operand: &hax::Operand,
    ) -> Result<(Operand, Ty), Error> {
        trace!();
        match operand {
            hax::Operand::Copy(place) => {
                let p = self.translate_place(span, place)?;
                let ty = p.ty().clone();
                Ok((Operand::Copy(p), ty))
            }
            hax::Operand::Move(place) => {
                let p = self.translate_place(span, place)?;
                let ty = p.ty().clone();
                Ok((Operand::Move(p), ty))
            }
            hax::Operand::Constant(const_op) => match &const_op.kind {
                hax::ConstOperandKind::Value(constant)
                | hax::ConstOperandKind::Promoted(_, Some(constant)) => {
                    let constant = self.translate_constant_expr_to_constant_expr(span, constant)?;
                    let ty = constant.ty.clone();
                    Ok((Operand::Const(constant), ty))
                }
                hax::ConstOperandKind::Promoted(promoted, None) => {
                    // A promoted constant that could not be evaluated.
                    // TODO: translate as a Global, then inline in a pass. will need to shift
                    // locals and block ids.
                    // TODO: disable hax's `inline_anon_const` so we also get that for inline
                    // consts too.
                    raise_error!(
                        self,
                        span,
                        "Cannot translate unevaluated constant: {promoted:?}"
                    )
                }
            },
        }
    }

    /// Translate an operand
    fn translate_operand(&mut self, span: Span, operand: &hax::Operand) -> Result<Operand, Error> {
        trace!();
        Ok(self.translate_operand_with_type(span, operand)?.0)
    }

    /// Translate an rvalue
    fn translate_rvalue(&mut self, span: Span, rvalue: &hax::Rvalue) -> Result<Rvalue, Error> {
        match rvalue {
            hax::Rvalue::Use(operand) => Ok(Rvalue::Use(self.translate_operand(span, operand)?)),
            hax::Rvalue::CopyForDeref(place) => {
                // According to the documentation, it seems to be an optimisation
                // for drop elaboration. We treat it as a regular copy.
                let place = self.translate_place(span, place)?;
                Ok(Rvalue::Use(Operand::Copy(place)))
            }
            hax::Rvalue::Repeat(operand, cnst) => {
                let c = self.translate_constant_expr_to_const_generic(span, cnst)?;
                let (operand, t) = self.translate_operand_with_type(span, operand)?;
                // Remark: we could desugar this into a function call later.
                Ok(Rvalue::Repeat(operand, t, c))
            }
            hax::Rvalue::Ref(_region, borrow_kind, place) => {
                let place = self.translate_place(span, place)?;
                let borrow_kind = translate_borrow_kind(*borrow_kind);
                Ok(Rvalue::Ref(place, borrow_kind))
            }
            hax::Rvalue::RawPtr(mtbl, place) => {
                let mtbl = match mtbl {
                    hax::RawPtrKind::Mut => RefKind::Mut,
                    hax::RawPtrKind::Const => RefKind::Shared,
                    hax::RawPtrKind::FakeForPtrMetadata => RefKind::Shared,
                };
                let place = self.translate_place(span, place)?;
                Ok(Rvalue::RawPtr(place, mtbl))
            }
            hax::Rvalue::Len(place) => {
                let place = self.translate_place(span, place)?;
                let ty = place.ty().clone();
                let cg = match ty.kind() {
                    TyKind::Adt(
                        TypeId::Builtin(aty @ (BuiltinTy::Array | BuiltinTy::Slice)),
                        generics,
                    ) => {
                        if aty.is_array() {
                            Some(generics.const_generics[0].clone())
                        } else {
                            None
                        }
                    }
                    _ => unreachable!(),
                };
                Ok(Rvalue::Len(place, ty, cg))
            }
            hax::Rvalue::Cast(cast_kind, operand, tgt_ty) => {
                trace!("Rvalue::Cast: {:?}", rvalue);
                // Translate the target type
                let tgt_ty = self.translate_ty(span, tgt_ty)?;

                // Translate the operand
                let (operand, src_ty) = self.translate_operand_with_type(span, operand)?;

                match cast_kind {
                    hax::CastKind::IntToInt
                    | hax::CastKind::IntToFloat
                    | hax::CastKind::FloatToInt
                    | hax::CastKind::FloatToFloat => {
                        let tgt_ty = *tgt_ty.kind().as_literal().unwrap();
                        let src_ty = *src_ty.kind().as_literal().unwrap();
                        Ok(Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::Scalar(src_ty, tgt_ty)),
                            operand,
                        ))
                    }
                    hax::CastKind::PtrToPtr
                    | hax::CastKind::PointerCoercion(hax::PointerCoercion::MutToConstPointer, ..)
                    | hax::CastKind::PointerCoercion(hax::PointerCoercion::ArrayToPointer, ..)
                    | hax::CastKind::PointerCoercion(hax::PointerCoercion::DynStar, ..)
                    | hax::CastKind::FnPtrToPtr
                    | hax::CastKind::PointerExposeProvenance
                    | hax::CastKind::PointerWithExposedProvenance => Ok(Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::RawPtr(src_ty, tgt_ty)),
                        operand,
                    )),
                    hax::CastKind::PointerCoercion(
                        hax::PointerCoercion::ClosureFnPointer(_)
                        | hax::PointerCoercion::UnsafeFnPointer
                        | hax::PointerCoercion::ReifyFnPointer,
                        ..,
                    ) => Ok(Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::FnPtr(src_ty, tgt_ty)),
                        operand,
                    )),
                    hax::CastKind::Transmute => Ok(Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::Transmute(src_ty, tgt_ty)),
                        operand,
                    )),
                    hax::CastKind::PointerCoercion(hax::PointerCoercion::Unsize, ..) => {
                        let unop = if let (
                            TyKind::Ref(
                                _,
                                deref!(TyKind::Adt(TypeId::Builtin(BuiltinTy::Array), generics)),
                                kind1,
                            ),
                            TyKind::Ref(
                                _,
                                deref!(TyKind::Adt(TypeId::Builtin(BuiltinTy::Slice), generics1)),
                                kind2,
                            ),
                        ) = (src_ty.kind(), tgt_ty.kind())
                        {
                            // In MIR terminology, we go from &[T; l] to &[T] which means we
                            // effectively "unsize" the type, as `l` no longer appears in the
                            // destination type. At runtime, the converse happens: the length
                            // materializes into the fat pointer.
                            assert!(
                                generics.types.elem_count() == 1
                                    && generics.const_generics.elem_count() == 1
                            );
                            assert!(generics.types[0] == generics1.types[0]);
                            assert!(kind1 == kind2);
                            UnOp::ArrayToSlice(
                                *kind1,
                                generics.types[0].clone(),
                                generics.const_generics[0].clone(),
                            )
                        } else {
                            UnOp::Cast(CastKind::Unsize(src_ty.clone(), tgt_ty.clone()))
                        };
                        Ok(Rvalue::UnaryOp(unop, operand))
                    }
                }
            }
            hax::Rvalue::BinaryOp(binop, (left, right)) => Ok(Rvalue::BinaryOp(
                self.translate_binaryop_kind(span, *binop)?,
                self.translate_operand(span, left)?,
                self.translate_operand(span, right)?,
            )),
            hax::Rvalue::NullaryOp(nullop, ty) => {
                trace!("NullOp: {:?}", nullop);
                let ty = self.translate_ty(span, ty)?;
                let op = match nullop {
                    hax::NullOp::SizeOf => NullOp::SizeOf,
                    hax::NullOp::AlignOf => NullOp::AlignOf,
                    hax::NullOp::OffsetOf(fields) => NullOp::OffsetOf(
                        fields
                            .iter()
                            .copied()
                            .map(|(n, idx)| (n, translate_field_id(idx)))
                            .collect(),
                    ),
                    hax::NullOp::UbChecks => NullOp::UbChecks,
                    hax::NullOp::ContractChecks => {
                        raise_error!(self, span, "charon does not support contracts");
                    }
                };
                Ok(Rvalue::NullaryOp(op, ty))
            }
            hax::Rvalue::UnaryOp(unop, operand) => {
                let unop = match unop {
                    hax::UnOp::Not => UnOp::Not,
                    hax::UnOp::Neg => UnOp::Neg,
                    hax::UnOp::PtrMetadata => UnOp::PtrMetadata,
                };
                Ok(Rvalue::UnaryOp(
                    unop,
                    self.translate_operand(span, operand)?,
                ))
            }
            hax::Rvalue::Discriminant(place) => {
                let place = self.translate_place(span, place)?;
                if let TyKind::Adt(TypeId::Adt(adt_id), _) = *place.ty().kind() {
                    Ok(Rvalue::Discriminant(place, adt_id))
                } else {
                    raise_error!(
                        self,
                        span,
                        "Unexpected scrutinee type for ReadDiscriminant: {}",
                        place.ty().fmt_with_ctx(&self.into_fmt())
                    )
                }
            }
            hax::Rvalue::Aggregate(aggregate_kind, operands) => {
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

                // First translate the operands
                let operands_t: Vec<Operand> = operands
                    .raw
                    .iter()
                    .map(|op| self.translate_operand(span, op))
                    .try_collect()?;

                match aggregate_kind {
                    hax::AggregateKind::Array(ty) => {
                        let t_ty = self.translate_ty(span, ty)?;
                        let cg = ConstGeneric::Value(Literal::Scalar(ScalarValue::Usize(
                            operands_t.len() as u64,
                        )));
                        Ok(Rvalue::Aggregate(
                            AggregateKind::Array(t_ty, cg),
                            operands_t,
                        ))
                    }
                    hax::AggregateKind::Tuple => Ok(Rvalue::Aggregate(
                        AggregateKind::Adt(
                            TypeId::Tuple,
                            None,
                            None,
                            GenericArgs::empty(GenericsSource::Builtin),
                        ),
                        operands_t,
                    )),
                    hax::AggregateKind::Adt(
                        adt_id,
                        variant_idx,
                        kind,
                        substs,
                        trait_refs,
                        user_annotation,
                        field_index,
                    ) => {
                        trace!("{:?}", rvalue);

                        // We ignore type annotations since rustc has already inferred all the
                        // types we need.
                        let _ = user_annotation;

                        let type_id = self.translate_type_id(span, adt_id)?;
                        // Sanity check
                        assert!(matches!(&type_id, TypeId::Adt(_)));

                        // Translate the substitution
                        let generics = self.translate_generic_args(
                            span,
                            substs,
                            trait_refs,
                            None,
                            type_id.generics_target(),
                        )?;

                        use hax::AdtKind;
                        let variant_id = match kind {
                            AdtKind::Struct | AdtKind::Union => None,
                            AdtKind::Enum => Some(translate_variant_id(*variant_idx)),
                        };
                        let field_id = match kind {
                            AdtKind::Struct | AdtKind::Enum => None,
                            AdtKind::Union => Some(translate_field_id(field_index.unwrap())),
                        };

                        let akind = AggregateKind::Adt(type_id, variant_id, field_id, generics);
                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    hax::AggregateKind::Closure(def_id, closure_args) => {
                        trace!(
                            "Closure:\n\n- def_id: {:?}\n\n- sig:\n{:?}",
                            def_id,
                            closure_args.tupled_sig
                        );

                        let fun_id = self.register_fun_decl_id(span, def_id);

                        // Retrieve the late-bound variables.
                        let binder = closure_args.tupled_sig.as_ref().rebind(());
                        // Translate the substitution
                        let generics = self.translate_generic_args(
                            span,
                            &closure_args.parent_args,
                            &closure_args.parent_trait_refs,
                            Some(binder),
                            GenericsSource::item(fun_id),
                        )?;

                        let akind = AggregateKind::Closure(fun_id, generics);

                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    hax::AggregateKind::RawPtr(ty, is_mut) => {
                        // TODO: replace with a call to `ptr::from_raw_parts`.
                        let t_ty = self.translate_ty(span, ty)?;
                        let mutability = if *is_mut {
                            RefKind::Mut
                        } else {
                            RefKind::Shared
                        };

                        let akind = AggregateKind::RawPtr(t_ty, mutability);

                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    hax::AggregateKind::Coroutine(..)
                    | hax::AggregateKind::CoroutineClosure(..) => {
                        raise_error!(self, span, "Coroutines are not supported");
                    }
                }
            }
            hax::Rvalue::ShallowInitBox(op, ty) => {
                let op = self.translate_operand(span, op)?;
                let ty = self.translate_ty(span, ty)?;
                Ok(Rvalue::ShallowInitBox(op, ty))
            }
            hax::Rvalue::ThreadLocalRef(_) => {
                raise_error!(
                    self,
                    span,
                    "charon does not support thread local references"
                );
            }
            hax::Rvalue::WrapUnsafeBinder { .. } => {
                raise_error!(
                    self,
                    span,
                    "charon does not support unsafe lifetime binders"
                );
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
    ) -> Result<Option<Statement>, Error> {
        trace!("About to translate statement (MIR) {:?}", statement);
        let span = self
            .t_ctx
            .translate_span_from_source_info(&body.source_scopes, &statement.source_info);

        use hax::StatementKind;
        let t_statement: Option<RawStatement> = match &*statement.kind {
            StatementKind::Assign((place, rvalue)) => {
                let t_place = self.translate_place(span, place)?;
                let t_rvalue = self.translate_rvalue(span, rvalue)?;
                Some(RawStatement::Assign(t_place, t_rvalue))
            }
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                let t_place = self.translate_place(span, place)?;
                let variant_id = translate_variant_id(*variant_index);
                Some(RawStatement::SetDiscriminant(t_place, variant_id))
            }
            StatementKind::StorageLive(local) => {
                let var_id = self.translate_local(local).unwrap();
                Some(RawStatement::StorageLive(var_id))
            }
            StatementKind::StorageDead(local) => {
                let var_id = self.translate_local(local).unwrap();
                Some(RawStatement::StorageDead(var_id))
            }
            StatementKind::Deinit(place) => {
                let t_place = self.translate_place(span, place)?;
                Some(RawStatement::Deinit(t_place))
            }
            // This asserts the operand true on pain of UB. We treat it like a normal assertion.
            StatementKind::Intrinsic(hax::NonDivergingIntrinsic::Assume(op)) => {
                let op = self.translate_operand(span, op)?;
                Some(RawStatement::Assert(Assert {
                    cond: op,
                    expected: true,
                    on_failure: AbortKind::UndefinedBehavior,
                }))
            }
            StatementKind::Intrinsic(hax::NonDivergingIntrinsic::CopyNonOverlapping(..)) => {
                raise_error!(self, span, "Unsupported statement kind: CopyNonOverlapping");
            }
            // This is for the stacked borrows memory model.
            StatementKind::Retag(_, _) => None,
            // These two are only there to make borrow-checking accept less code, and are removed
            // in later MIRs.
            StatementKind::FakeRead(..) | StatementKind::PlaceMention(..) => None,
            // There are user-provided type annotations with no semantic effect (since we get a
            // fully-typechecked MIR (TODO: this isn't quite true with opaque types, we should
            // really use promoted MIR)).
            StatementKind::AscribeUserType(_, _) => None,
            // Used for coverage instrumentation.
            StatementKind::Coverage(_) => None,
            // Used in the interpreter to check that const code doesn't run for too long or even
            // indefinitely.
            StatementKind::ConstEvalCounter => None,
            // Semantically equivalent to `Nop`, used only for rustc lints.
            StatementKind::BackwardIncompatibleDropHint { .. } => None,
            StatementKind::Nop => None,
        };

        // Add the span information
        Ok(t_statement.map(|kind| Statement::new(span, kind)))
    }

    /// Translate a terminator
    fn translate_terminator(
        &mut self,
        body: &hax::MirBody<()>,
        terminator: &hax::Terminator,
        statements: &mut Vec<Statement>,
    ) -> Result<Terminator, Error> {
        trace!("About to translate terminator (MIR) {:?}", terminator);
        // Compute the span information beforehand (we might need it to introduce
        // intermediate statements - we desugar some terminators)
        let span = self
            .t_ctx
            .translate_span_from_source_info(&body.source_scopes, &terminator.source_info);

        // Translate the terminator
        use hax::TerminatorKind;
        let t_terminator: RawTerminator = match &terminator.kind {
            TerminatorKind::Goto { target } => {
                let target = self.translate_basic_block_id(*target);
                RawTerminator::Goto { target }
            }
            TerminatorKind::SwitchInt {
                discr,
                targets,
                otherwise,
                ..
            } => {
                // Translate the operand which gives the discriminant
                let (discr, discr_ty) = self.translate_operand_with_type(span, discr)?;

                // Translate the switch targets
                let targets = self.translate_switch_targets(span, &discr_ty, targets, otherwise)?;

                RawTerminator::Switch { discr, targets }
            }
            TerminatorKind::UnwindResume => {
                // This is used to correctly unwind. We shouldn't get there: if
                // we panic, the state gets stuck.
                raise_error!(self, span, "Unexpected terminator: UnwindResume");
            }
            TerminatorKind::UnwindTerminate { .. } => {
                raise_error!(self, span, "Unexpected terminator: UnwindTerminate")
            }
            TerminatorKind::Return => RawTerminator::Return,
            // A MIR `Unreachable` terminator indicates undefined behavior of the rust abstract
            // machine.
            TerminatorKind::Unreachable => RawTerminator::Abort(AbortKind::UndefinedBehavior),
            TerminatorKind::Drop {
                place,
                target,
                unwind: _, // We consider that panic is an error, and don't model unwinding
                replace: _,
            } => {
                let place = self.translate_place(span, place)?;
                statements.push(Statement::new(span, RawStatement::Drop(place)));
                let target = self.translate_basic_block_id(*target);
                RawTerminator::Goto { target }
            }
            TerminatorKind::Call {
                fun,
                args,
                destination,
                target,
                unwind: _, // We model unwinding as an effet, we don't represent it in control flow
                fn_span: _,
                ..
            } => self.translate_function_call(statements, span, fun, args, destination, target)?,
            TerminatorKind::Assert {
                cond,
                expected,
                msg: _,
                target,
                unwind: _, // We model unwinding as an effet, we don't represent it in control flow
            } => {
                let assert = Assert {
                    cond: self.translate_operand(span, cond)?,
                    expected: *expected,
                    on_failure: AbortKind::Panic(None),
                };
                statements.push(Statement::new(span, RawStatement::Assert(assert)));
                let target = self.translate_basic_block_id(*target);
                RawTerminator::Goto { target }
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
                let target = self.translate_basic_block_id(*real_target);
                RawTerminator::Goto { target }
            }
            TerminatorKind::FalseUnwind {
                real_target,
                unwind: _,
            } => {
                // We consider this to be a goto
                let target = self.translate_basic_block_id(*real_target);
                RawTerminator::Goto { target }
            }
            TerminatorKind::InlineAsm { .. } => {
                raise_error!(self, span, "Inline assembly is not supported");
            }
            TerminatorKind::CoroutineDrop
            | TerminatorKind::TailCall { .. }
            | TerminatorKind::Yield { .. } => {
                raise_error!(self, span, "Unsupported terminator: {:?}", terminator.kind);
            }
        };

        // Add the span information
        Ok(Terminator::new(span, t_terminator))
    }

    /// Translate switch targets
    fn translate_switch_targets(
        &mut self,
        span: Span,
        switch_ty: &Ty,
        targets: &[(hax::ScalarInt, hax::BasicBlock)],
        otherwise: &hax::BasicBlock,
    ) -> Result<SwitchTargets, Error> {
        trace!("targets: {:?}", targets);
        let switch_ty = *switch_ty.kind().as_literal().unwrap();
        match switch_ty {
            LiteralTy::Bool => {
                assert_eq!(targets.len(), 1);
                let (val, target) = targets.first().unwrap();
                // It seems the block targets are inverted
                assert_eq!(val.data_le_bytes, [0; 16]);
                let if_block = self.translate_basic_block_id(*otherwise);
                let then_block = self.translate_basic_block_id(*target);
                Ok(SwitchTargets::If(if_block, then_block))
            }
            LiteralTy::Integer(int_ty) => {
                let targets: Vec<(ScalarValue, BlockId)> = targets
                    .iter()
                    .map(|(v, tgt)| {
                        let v = ScalarValue::from_le_bytes(int_ty, v.data_le_bytes);
                        let tgt = self.translate_basic_block_id(*tgt);
                        Ok((v, tgt))
                    })
                    .try_collect()?;
                let otherwise = self.translate_basic_block_id(*otherwise);
                Ok(SwitchTargets::SwitchInt(int_ty, targets, otherwise))
            }
            _ => raise_error!(self, span, "Can't match on type {switch_ty}"),
        }
    }

    /// Translate a function call statement.
    /// Note that `body` is the body of the function being translated, not of the
    /// function referenced in the function call: we need it in order to translate
    /// the blocks we go to after the function call returns.
    #[allow(clippy::too_many_arguments)]
    fn translate_function_call(
        &mut self,
        statements: &mut Vec<Statement>,
        span: Span,
        fun: &hax::FunOperand,
        args: &Vec<hax::Spanned<hax::Operand>>,
        destination: &hax::Place,
        target: &Option<hax::BasicBlock>,
    ) -> Result<RawTerminator, Error> {
        trace!();
        // There are two cases, depending on whether this is a "regular"
        // call to a top-level function identified by its id, or if we
        // are using a local function pointer (i.e., the operand is a "move").
        let lval = self.translate_place(span, destination)?;
        // Translate the function operand.
        let fn_operand = match fun {
            hax::FunOperand::Static {
                def_id,
                generics,
                trait_refs,
                trait_info,
            } => {
                trace!("func: {:?}", def_id);
                let fun_def = self.t_ctx.hax_def(def_id)?;
                let name = self.t_ctx.hax_def_id_to_name(&fun_def.def_id)?;
                let panic_lang_items = &["panic", "panic_fmt", "begin_panic"];
                let panic_names = &[&["core", "panicking", "assert_failed"], EXPLICIT_PANIC_NAME];

                if fun_def
                    .lang_item
                    .as_deref()
                    .is_some_and(|lang_it| panic_lang_items.iter().contains(&lang_it))
                    || panic_names.iter().any(|panic| name.equals_ref_name(panic))
                {
                    // If the call is `panic!`, then the target is `None`.
                    // I don't know in which other cases it can be `None`.
                    assert!(target.is_none());
                    // We ignore the arguments
                    return Ok(RawTerminator::Abort(AbortKind::Panic(Some(name))));
                } else {
                    let fn_ptr =
                        self.translate_fn_ptr(span, def_id, generics, trait_refs, trait_info)?;
                    FnOperand::Regular(fn_ptr)
                }
            }
            hax::FunOperand::DynamicMove(p) => {
                // Call to a local function pointer
                let p = self.translate_place(span, p)?;

                // TODO: we may have a problem here because as we don't
                // know which function is being called, we may not be
                // able to filter the arguments properly... But maybe
                // this is rather an issue for the statement which creates
                // the function pointer, by refering to a top-level function
                // for instance.
                FnOperand::Move(p)
            }
        };
        let args = self.translate_arguments(span, args)?;
        let call = Call {
            func: fn_operand,
            args,
            dest: lval,
        };
        statements.push(Statement::new(span, RawStatement::Call(call)));
        Ok(match target {
            Some(target) => {
                let target = self.translate_basic_block_id(*target);
                RawTerminator::Goto { target }
            }
            None => RawTerminator::Abort(AbortKind::UndefinedBehavior),
        })
    }

    /// Evaluate function arguments in a context, and return the list of computed
    /// values.
    fn translate_arguments(
        &mut self,
        span: Span,
        args: &Vec<hax::Spanned<hax::Operand>>,
    ) -> Result<Vec<Operand>, Error> {
        let mut t_args: Vec<Operand> = Vec::new();
        for arg in args.iter().map(|x| &x.node) {
            // Translate
            let op = self.translate_operand(span, arg)?;
            t_args.push(op);
        }
        Ok(t_args)
    }

    /// Gather all the lines that start with `//` inside the given span.
    fn translate_body_comments(
        &mut self,
        def: &hax::FullDef,
        charon_span: Span,
    ) -> Vec<(usize, Vec<String>)> {
        if let Some(body_text) = &def.source_text {
            let mut comments = body_text
                .lines()
                // Iter through the lines of this body in reverse order.
                .rev()
                .enumerate()
                // Compute the absolute line number
                .map(|(i, line)| (charon_span.span.end.line - i, line))
                // Extract the comment if this line starts with `//`
                .map(|(line_nbr, line)| (line_nbr, line.trim_start().strip_prefix("//")))
                .peekable()
                .batching(|iter| {
                    // Get the next line. This is not a comment: it's either the last line of the
                    // body or a line that wasn't consumed by `peeking_take_while`.
                    let (line_nbr, _first) = iter.next()?;
                    // Collect all the comments before this line.
                    let mut comments = iter
                        // `peeking_take_while` ensures we don't consume a line that returns
                        // `false`. It will be consumed by the next round of `batching`.
                        .peeking_take_while(|(_, opt_comment)| opt_comment.is_some())
                        .map(|(_, opt_comment)| opt_comment.unwrap())
                        .map(|s| s.strip_prefix(" ").unwrap_or(s))
                        .map(str::to_owned)
                        .collect_vec();
                    comments.reverse();
                    Some((line_nbr, comments))
                })
                .filter(|(_, comments)| !comments.is_empty())
                .collect_vec();
            comments.reverse();
            comments
        } else {
            Vec::new()
        }
    }

    /// Translate a function body if we can (it has MIR) and we want to (we don't translate bodies
    /// declared opaque, and only translate non-local bodies if `extract_opaque_bodies` is set).
    fn translate_body(
        &mut self,
        span: Span,
        def: &hax::FullDef,
    ) -> Result<Result<Body, Opaque>, Error> {
        // Stopgap measure because there are still many panics in charon and hax.
        let mut this = panic::AssertUnwindSafe(&mut *self);
        let res = panic::catch_unwind(move || this.translate_body_aux(def, span));
        match res {
            Ok(Ok(body)) => Ok(body),
            // Translation error
            Ok(Err(e)) => Err(e),
            Err(_) => {
                raise_error!(self, span, "Thread panicked when extracting body.");
            }
        }
    }

    fn translate_body_aux(
        &mut self,
        def: &hax::FullDef,
        span: Span,
    ) -> Result<Result<Body, Opaque>, Error> {
        // Retrieve the body
        let rust_id = def.rust_def_id();
        let Some(body) = self.t_ctx.get_mir(rust_id, span)? else {
            return Ok(Err(Opaque));
        };

        // Compute the span information
        let span = self.translate_span_from_hax(&body.span);

        // Initialize the local variables
        trace!("Translating the body locals");
        self.locals.arg_count = body.arg_count;
        self.translate_body_locals(&body)?;

        // Translate the expression body
        trace!("Translating the expression body");

        // Register the start block
        let id = self.translate_basic_block_id(rustc_index::Idx::new(mir::START_BLOCK.as_usize()));
        assert!(id == START_BLOCK_ID);

        // For as long as there are blocks in the stack, translate them
        while let Some(hax_block_id) = self.blocks_stack.pop_front() {
            let hax_block = body.basic_blocks.get(hax_block_id).unwrap();
            let block_id = self.translate_basic_block_id(hax_block_id);
            let block = self.translate_basic_block(&body, hax_block)?;
            self.blocks.set_slot(block_id, block);
        }

        // Create the body
        Ok(Ok(Body::Unstructured(ExprBody {
            span,
            locals: mem::take(&mut self.locals),
            body: mem::take(&mut self.blocks),
            comments: self.translate_body_comments(def, span),
        })))
    }
}

impl ItemTransCtx<'_, '_> {
    pub(crate) fn get_item_kind(
        &mut self,
        span: Span,
        def: &hax::FullDef,
    ) -> Result<ItemKind, Error> {
        let assoc = match def.kind() {
            hax::FullDefKind::AssocTy {
                associated_item, ..
            }
            | hax::FullDefKind::AssocConst {
                associated_item, ..
            }
            | hax::FullDefKind::AssocFn {
                associated_item, ..
            } => associated_item,
            _ => return Ok(ItemKind::Regular),
        };
        Ok(match &assoc.container {
            // E.g.:
            // ```
            // impl<T> List<T> {
            //   fn new() -> Self { ... } <- inherent method
            // }
            // ```
            hax::AssocItemContainer::InherentImplContainer { .. } => ItemKind::Regular,
            // E.g.:
            // ```
            // impl Foo for Bar {
            //   fn baz(...) { ... } // <- implementation of a trait method
            // }
            // ```
            hax::AssocItemContainer::TraitImplContainer {
                impl_id,
                impl_generics,
                impl_required_impl_exprs,
                implemented_trait_ref,
                implemented_trait_item,
                overrides_default,
                ..
            } => {
                let impl_id = self.register_trait_impl_id(span, impl_id);
                let impl_ref = TraitImplRef {
                    impl_id,
                    generics: self.translate_generic_args(
                        span,
                        impl_generics,
                        impl_required_impl_exprs,
                        None,
                        GenericsSource::item(impl_id),
                    )?,
                };
                let trait_ref = self.translate_trait_ref(span, implemented_trait_ref)?;
                if matches!(def.kind(), hax::FullDefKind::AssocFn { .. }) {
                    // Ensure we translate the corresponding decl signature.
                    // FIXME(self_clause): also ensure we translate associated globals
                    // consistently; to do once we have clearer `Self` clause handling.
                    let _ = self.register_fun_decl_id(span, implemented_trait_item);
                }
                ItemKind::TraitImpl {
                    impl_ref,
                    trait_ref,
                    item_name: TraitItemName(assoc.name.clone()),
                    reuses_default: !overrides_default,
                }
            }
            // This method is the *declaration* of a trait item
            // E.g.:
            // ```
            // trait Foo {
            //   fn baz(...); // <- declaration of a trait method
            // }
            // ```
            hax::AssocItemContainer::TraitContainer { trait_ref, .. } => {
                // The trait id should be Some(...): trait markers (that we may eliminate)
                // don't have associated items.
                let trait_ref = self.translate_trait_ref(span, trait_ref)?;
                let item_name = TraitItemName(assoc.name.clone());
                ItemKind::TraitDecl {
                    trait_ref,
                    item_name,
                    has_default: assoc.has_value,
                }
            }
        })
    }

    /// Translate a function's signature, and initialize a body translation context
    /// at the same time - the function signature gives us the list of region and
    /// type parameters, that we put in the translation context.
    fn translate_function_signature(
        &mut self,
        def: &hax::FullDef,
        item_meta: &ItemMeta,
    ) -> Result<FunSig, Error> {
        let span = item_meta.span;

        self.translate_def_generics(span, def)?;

        let signature = match &def.kind {
            hax::FullDefKind::Closure { args, .. } => &args.tupled_sig,
            hax::FullDefKind::Fn { sig, .. } => sig,
            hax::FullDefKind::AssocFn { sig, .. } => sig,
            hax::FullDefKind::Ctor {
                fields, output_ty, ..
            } => {
                let sig = hax::TyFnSig {
                    inputs: fields.iter().map(|field| field.ty.clone()).collect(),
                    output: output_ty.clone(),
                    c_variadic: false,
                    safety: hax::Safety::Safe,
                    abi: hax::ExternAbi::Rust,
                };
                &hax::Binder {
                    value: sig,
                    bound_vars: Default::default(),
                }
            }
            hax::FullDefKind::Const { ty, .. }
            | hax::FullDefKind::AssocConst { ty, .. }
            | hax::FullDefKind::AnonConst { ty, .. }
            | hax::FullDefKind::InlineConst { ty, .. }
            | hax::FullDefKind::Static { ty, .. } => {
                let sig = hax::TyFnSig {
                    inputs: vec![],
                    output: ty.clone(),
                    c_variadic: false,
                    safety: hax::Safety::Safe,
                    abi: hax::ExternAbi::Rust,
                };
                &hax::Binder {
                    value: sig,
                    bound_vars: Default::default(),
                }
            }
            _ => panic!("Unexpected definition for function: {def:?}"),
        };

        // Translate the signature
        trace!("signature of {:?}:\n{:?}", def.def_id, signature.value);
        let mut inputs: Vec<Ty> = signature
            .value
            .inputs
            .iter()
            .map(|ty| self.translate_ty(span, ty))
            .try_collect()?;
        let output = self.translate_ty(span, &signature.value.output)?;

        let fmt_ctx = self.into_fmt();
        trace!(
            "# Input variables types:\n{}",
            pretty_display_list(|x| fmt_ctx.format_object(x), &inputs)
        );
        trace!(
            "# Output variable type:\n{}",
            fmt_ctx.format_object(&output)
        );

        let is_unsafe = match signature.value.safety {
            hax::Safety::Unsafe => true,
            hax::Safety::Safe => false,
        };

        let closure_info = match &def.kind {
            hax::FullDefKind::Closure { args, .. } => {
                let kind = match args.kind {
                    hax::ClosureKind::Fn => ClosureKind::Fn,
                    hax::ClosureKind::FnMut => ClosureKind::FnMut,
                    hax::ClosureKind::FnOnce => ClosureKind::FnOnce,
                };

                assert_eq!(inputs.len(), 1);
                let tuple_arg = inputs.pop().unwrap();

                let state: Vector<TypeVarId, Ty> = args
                    .upvar_tys
                    .iter()
                    .map(|ty| self.translate_ty(span, &ty))
                    .try_collect()?;
                // Add the state of the closure as first parameter.
                let state_ty = {
                    // Group the state types into a tuple
                    let state_ty =
                        TyKind::Adt(TypeId::Tuple, GenericArgs::new_for_builtin(state.clone()))
                            .into_ty();
                    // Depending on the kind of the closure, add a reference
                    match &kind {
                        ClosureKind::FnOnce => state_ty,
                        ClosureKind::Fn | ClosureKind::FnMut => {
                            let rid = self
                                .innermost_generics_mut()
                                .regions
                                .push_with(|index| RegionVar { index, name: None });
                            let r = Region::Var(DeBruijnVar::new_at_zero(rid));
                            let mutability = if kind == ClosureKind::Fn {
                                RefKind::Shared
                            } else {
                                RefKind::Mut
                            };
                            TyKind::Ref(r, state_ty, mutability).into_ty()
                        }
                    }
                };
                inputs.push(state_ty);

                // Unpack the tupled arguments to match the body locals.
                let TyKind::Adt(TypeId::Tuple, tuple_args) = tuple_arg.kind() else {
                    raise_error!(self, span, "Closure argument is not a tuple")
                };
                inputs.extend(tuple_args.types.iter().cloned());

                Some(ClosureInfo { kind, state })
            }
            _ => None,
        };

        Ok(FunSig {
            generics: self.the_only_binder().params.clone(),
            is_unsafe,
            is_closure: matches!(&def.kind, hax::FullDefKind::Closure { .. }),
            closure_info,
            inputs,
            output,
        })
    }

    /// Generate a fake function body for ADT constructors.
    fn build_ctor_body(
        &mut self,
        span: Span,
        signature: &FunSig,
        adt_def_id: &hax::DefId,
        ctor_of: &hax::CtorOf,
        variant_id: usize,
        fields: &hax::IndexVec<hax::FieldIdx, hax::FieldDef>,
        output_ty: &hax::Ty,
    ) -> Result<Body, Error> {
        let adt_decl_id = self.register_type_decl_id(span, adt_def_id);
        let output_ty = self.translate_ty(span, output_ty)?;
        let mut locals = Locals {
            arg_count: fields.len(),
            locals: Vector::new(),
        };
        locals.new_var(None, output_ty);
        let args: Vec<_> = fields
            .iter()
            .map(|field| {
                let ty = self.translate_ty(span, &field.ty)?;
                let place = locals.new_var(None, ty);
                Ok(Operand::Move(place))
            })
            .try_collect()?;
        let variant = match ctor_of {
            hax::CtorOf::Struct => None,
            hax::CtorOf::Variant => Some(VariantId::from(variant_id)),
        };
        let st_kind = RawStatement::Assign(
            locals.return_place(),
            Rvalue::Aggregate(
                AggregateKind::Adt(
                    TypeId::Adt(adt_decl_id),
                    variant,
                    None,
                    signature
                        .generics
                        .identity_args(GenericsSource::item(adt_decl_id)),
                ),
                args,
            ),
        );
        let statement = Statement::new(span, st_kind);
        let block = BlockData {
            statements: vec![statement],
            terminator: Terminator::new(span, RawTerminator::Return),
        };
        let body = Body::Unstructured(GExprBody {
            span,
            locals,
            comments: Default::default(),
            body: [block].into_iter().collect(),
        });
        Ok(body)
    }

    /// Auxiliary function to translate function calls and references to functions.
    /// Translate a function id applied with some substitutions.
    ///
    /// TODO: should we always erase the regions?
    pub(crate) fn translate_fn_ptr(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
        substs: &Vec<hax::GenericArg>,
        trait_refs: &Vec<hax::ImplExpr>,
        trait_info: &Option<hax::ImplExpr>,
    ) -> Result<FnPtr, Error> {
        let fun_def = self.t_ctx.hax_def(def_id)?;

        // Trait information
        trace!(
            "Trait information:\n- def_id: {:?}\n- impl source:\n{:?}",
            def_id,
            trait_info
        );
        trace!(
            "Method traits:\n- def_id: {:?}\n- traits:\n{:?}",
            def_id,
            trait_refs
        );

        // Check if the function is considered primitive: primitive
        // functions benefit from special treatment.
        let fun_id = if fun_def.diagnostic_item.as_deref() == Some("box_new") {
            // Built-in function.
            assert!(trait_info.is_none());
            FunIdOrTraitMethodRef::Fun(FunId::Builtin(BuiltinFunId::BoxNew))
        } else {
            let fun_id = self.register_fun_decl_id(span, def_id);
            // Two cases depending on whether we call a trait method or not
            match trait_info {
                // Direct function call
                None => FunIdOrTraitMethodRef::Fun(FunId::Regular(fun_id)),
                // Trait method
                Some(trait_info) => {
                    let impl_expr = self.translate_trait_impl_expr(span, trait_info)?;
                    let method_name = self.t_ctx.translate_trait_item_name(def_id)?;
                    FunIdOrTraitMethodRef::Trait(impl_expr, method_name, fun_id)
                }
            }
        };

        // Translate the type parameters
        let binder = match fun_def.kind() {
            hax::FullDefKind::Fn { sig, .. } | hax::FullDefKind::AssocFn { sig, .. } => {
                Some(sig.as_ref().rebind(()))
            }
            _ => None,
        };
        let generics = self.translate_generic_args(
            span,
            substs,
            trait_refs,
            binder,
            fun_id.generics_target(),
        )?;

        Ok(FnPtr {
            func: fun_id,
            generics,
        })
    }

    /// Translate one function.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_function(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<FunDecl, Error> {
        trace!("About to translate function:\n{:?}", def.def_id);
        let span = item_meta.span;

        // Translate the function signature
        trace!("Translating function signature");
        let signature = self.translate_function_signature(def, &item_meta)?;

        // Check whether this function is a method declaration for a trait definition.
        // If this is the case, it shouldn't contain a body.
        let kind = self.get_item_kind(span, def)?;
        let is_trait_method_decl_without_default = match &kind {
            ItemKind::Regular | ItemKind::TraitImpl { .. } => false,
            ItemKind::TraitDecl { has_default, .. } => !has_default,
        };

        let is_global_initializer = matches!(
            def.kind(),
            hax::FullDefKind::Const { .. }
                | hax::FullDefKind::AssocConst { .. }
                | hax::FullDefKind::AnonConst { .. }
                | hax::FullDefKind::InlineConst { .. }
                | hax::FullDefKind::Static { .. }
        );
        let is_global_initializer =
            is_global_initializer.then(|| self.register_global_decl_id(span, &def.def_id));

        let body_id = if item_meta.opacity.with_private_contents().is_opaque()
            || is_trait_method_decl_without_default
        {
            Err(Opaque)
        } else if let hax::FullDefKind::Ctor {
            adt_def_id,
            ctor_of,
            variant_id,
            fields,
            output_ty,
            ..
        } = def.kind()
        {
            let body = self.build_ctor_body(
                span,
                &signature,
                adt_def_id,
                ctor_of,
                *variant_id,
                fields,
                output_ty,
            )?;
            Ok(body)
        } else {
            // Translate the body. This doesn't store anything if we can't/decide not to translate
            // this body.
            let mut bt_ctx = BodyTransCtx::new(&mut self);
            match bt_ctx.translate_body(item_meta.span, def) {
                Ok(Ok(body)) => Ok(body),
                // Opaque declaration
                Ok(Err(Opaque)) => Err(Opaque),
                // Translation error.
                // FIXME: handle error cases more explicitly.
                Err(_) => Err(Opaque),
            }
        };
        Ok(FunDecl {
            def_id,
            item_meta,
            signature,
            kind,
            is_global_initializer,
            body: body_id,
        })
    }

    /// Translate one global.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_global(
        mut self,
        def_id: GlobalDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<GlobalDecl, Error> {
        trace!("About to translate global:\n{:?}", def.def_id);
        let span = item_meta.span;

        // Translate the generics and predicates - globals *can* have generics
        // Ex.:
        // ```
        // impl<const N : usize> Foo<N> {
        //   const LEN : usize = N;
        // }
        // ```
        self.translate_def_generics(span, def)?;

        // Retrieve the kind
        let global_kind = self.get_item_kind(span, def)?;

        trace!("Translating global type");
        let ty = match &def.kind {
            hax::FullDefKind::Const { ty, .. }
            | hax::FullDefKind::AssocConst { ty, .. }
            | hax::FullDefKind::AnonConst { ty, .. }
            | hax::FullDefKind::InlineConst { ty, .. }
            | hax::FullDefKind::Static { ty, .. } => ty,
            _ => panic!("Unexpected def for constant: {def:?}"),
        };
        let ty = self.translate_ty(span, ty)?;

        let initializer = self.register_fun_decl_id(span, &def.def_id);

        Ok(GlobalDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            ty,
            kind: global_kind,
            init: initializer,
        })
    }
}
