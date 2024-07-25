//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

use std::mem;
use std::panic;
use std::rc::Rc;

use super::get_mir::{boxes_are_desugared, get_mir_for_def_id_and_level};
use super::translate_ctx::*;
use super::translate_types;
use charon_lib::ast::*;
use charon_lib::common::*;
use charon_lib::formatter::{Formatter, IntoFormatter};
use charon_lib::ids::Vector;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::ullbc_ast::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::{HasMirSetter, HasOwnerIdSetter, SInto};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::START_BLOCK;
use translate_types::translate_bound_region_kind_name;

pub(crate) struct SubstFunId {
    pub func: FnPtr,
    pub args: Option<Vec<Operand>>,
}

pub(crate) enum SubstFunIdOrPanic {
    Panic(Name),
    Fun(SubstFunId),
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
            hax::MutBorrowKind::ClosureCapture => unimplemented!(),
        },
        hax::BorrowKind::Fake(hax::FakeBorrowKind::Shallow) => BorrowKind::Shallow,
        // This one is used only in deref patterns.
        hax::BorrowKind::Fake(hax::FakeBorrowKind::Deep) => unimplemented!(),
    }
}

fn translate_unaryop_kind(binop: hax::UnOp) -> UnOp {
    match binop {
        hax::UnOp::Not => UnOp::Not,
        hax::UnOp::Neg => UnOp::Neg,
        hax::UnOp::PtrMetadata => unimplemented!("Unop::PtrMetadata"),
    }
}

impl<'tcx, 'ctx> TranslateCtx<'tcx, 'ctx> {
    fn translate_binaryop_kind(
        &mut self,
        span: rustc_span::Span,
        binop: hax::BinOp,
    ) -> Result<BinOp, Error> {
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
            hax::BinOp::Cmp => {
                error_or_panic!(self, span, "Unsupported binary operation: Cmp")
            }
            hax::BinOp::Offset => {
                error_or_panic!(self, span, "Unsupported binary operation: offset")
            }
        })
    }

    pub(crate) fn get_item_kind(
        &mut self,
        src: &Option<DepSource>,
        def: &hax::Def,
    ) -> Result<ItemKind, Error> {
        let assoc_item = match def {
            hax::Def::AssocTy {
                associated_item, ..
            }
            | hax::Def::AssocConst {
                associated_item, ..
            }
            | hax::Def::AssocFn {
                associated_item, ..
            } => Some(associated_item),
            _ => None,
        };
        Ok(match assoc_item {
            None => ItemKind::Regular,
            Some(assoc) => {
                match &assoc.container {
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
                        implemented_trait,
                        implemented_trait_item,
                        overrides_default,
                    } => {
                        // The trait id should be Some(...): trait markers (that we may eliminate)
                        // don't have methods.
                        let trait_id = self
                            .register_trait_decl_id(src, implemented_trait.into())?
                            .unwrap();

                        let impl_id = self.register_trait_impl_id(src, impl_id.into())?.unwrap();

                        let item_name =
                            self.translate_trait_item_name(implemented_trait_item.into())?;

                        ItemKind::TraitItemImpl {
                            impl_id,
                            trait_id,
                            item_name,
                            provided: *overrides_default,
                        }
                    }
                    // This method is the *declaration* of a trait item
                    // E.g.:
                    // ```
                    // trait Foo {
                    //   fn baz(...); // <- declaration of a trait method
                    // }
                    // ```
                    hax::AssocItemContainer::TraitContainer { trait_id } => {
                        // The trait id should be Some(...): trait markers (that we may eliminate)
                        // don't have associated items.
                        let trait_id = self.register_trait_decl_id(src, trait_id.into())?.unwrap();
                        let item_name = TraitItemName(assoc.name.clone());

                        // Check whether this item has a provided value.
                        if assoc.has_value {
                            ItemKind::TraitItemProvided(trait_id, item_name)
                        } else {
                            ItemKind::TraitItemDecl(trait_id, item_name)
                        }
                    }
                }
            }
        })
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Translate a function's local variables by adding them in the environment.
    fn translate_body_locals(&mut self, body: &hax::MirBody<()>) -> Result<(), Error> {
        // Translate the parameters
        for (index, var) in body.local_decls.raw.iter().enumerate() {
            trace!("Translating local of index {} and type {:?}", index, var.ty);

            // Find the name of the variable
            let name: Option<String> = var.name.clone();

            // Translate the type
            let erase_regions = true;
            let span = var.source_info.span.rust_span_data.unwrap().span();
            let ty = self.translate_ty(span, erase_regions, &var.ty)?;

            // Add the variable to the environment
            self.push_var(index, ty, name);
        }

        Ok(())
    }

    /// Translate an expression's body (either a function or a global).
    ///
    /// The local variables should already have been translated and inserted in
    /// the context.
    fn translate_transparent_expression_body(
        &mut self,
        body: &hax::MirBody<()>,
    ) -> Result<(), Error> {
        trace!();

        // Register the start block
        let id = self.translate_basic_block_id(rustc_index::Idx::new(START_BLOCK.as_usize()));
        assert!(id == START_BLOCK_ID);

        // For as long as there are blocks in the stack, translate them
        while let Some(block_id) = self.blocks_stack.pop_front() {
            self.translate_basic_block(body, block_id)?;
        }

        Ok(())
    }

    /// Translate a basic block id and register it, if it hasn't been done.
    fn translate_basic_block_id(&mut self, block_id: hax::BasicBlock) -> BlockId {
        match self.blocks_map.get(&block_id) {
            None => {
                // Generate a fresh id - this also registers the block
                self.fresh_block_id(block_id)
            }
            Some(id) => id,
        }
    }

    fn translate_basic_block(
        &mut self,
        body: &hax::MirBody<()>,
        block_id: hax::BasicBlock,
    ) -> Result<(), Error> {
        // Retrieve the translated block id
        let nid = self.translate_basic_block_id(block_id);

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
        let terminator = block.terminator.as_ref().unwrap();
        let terminator = self.translate_terminator(body, terminator)?;

        // Insert the block in the translated blocks
        let block = BlockData {
            statements,
            terminator,
        };

        self.push_block(nid, block);

        Ok(())
    }

    /// Translate a place and return its type
    fn translate_place_with_type(
        &mut self,
        span: rustc_span::Span,
        place: &hax::Place,
    ) -> Result<(Place, Ty), Error> {
        let erase_regions = true;
        let ty = self.translate_ty(span, erase_regions, &place.ty)?;
        let (var_id, projection) = self.translate_projection(span, place)?;
        Ok((Place { var_id, projection }, ty))
    }

    /// Translate a place
    fn translate_place(
        &mut self,
        span: rustc_span::Span,
        place: &hax::Place,
    ) -> Result<Place, Error> {
        Ok(self.translate_place_with_type(span, place)?.0)
    }

    /// Translate a place - TODO: rename
    /// TODO: Hax represents places in a different manner than MIR. We should
    /// update our representation of places to match the Hax representation.
    fn translate_projection(
        &mut self,
        span: rustc_span::Span,
        place: &hax::Place,
    ) -> Result<(VarId, Projection), Error> {
        let erase_regions = true;
        match &place.kind {
            hax::PlaceKind::Local(local) => {
                let var_id = self.get_local(local).unwrap();
                Ok((var_id, Vec::new()))
            }
            hax::PlaceKind::Projection { place, kind } => {
                let (var_id, mut projection) = self.translate_projection(span, place)?;
                // Compute the type of the value *before* projection - we use this
                // to disambiguate
                let current_ty = self.translate_ty(span, erase_regions, &place.ty)?;
                match kind {
                    hax::ProjectionElem::Deref => {
                        // We use the type to disambiguate
                        match current_ty {
                            Ty::Ref(_, _, _) => {
                                projection.push(ProjectionElem::Deref);
                            }
                            Ty::Adt(TypeId::Assumed(AssumedTy::Box), generics) => {
                                // This case only happens in some MIR levels
                                assert!(!boxes_are_desugared(self.t_ctx.options.mir_level));
                                assert!(generics.regions.is_empty());
                                assert!(generics.types.len() == 1);
                                assert!(generics.const_generics.is_empty());
                                projection.push(ProjectionElem::DerefBox);
                            }
                            Ty::RawPtr(_, _) => {
                                projection.push(ProjectionElem::DerefRawPtr);
                            }
                            _ => {
                                unreachable!(
                                    "\n- place.kind: {:?}\n- current_ty: {:?}",
                                    kind, current_ty
                                );
                            }
                        }
                    }
                    hax::ProjectionElem::Field(field_kind) => {
                        use hax::ProjectionElemFieldKind::*;
                        let proj_elem = match field_kind {
                            Tuple(id) => {
                                let (_, generics) = current_ty.as_adt();
                                let field_id = translate_field_id(*id);
                                let proj_kind = FieldProjKind::Tuple(generics.types.len());
                                ProjectionElem::Field(proj_kind, field_id)
                            }
                            Adt {
                                typ: _,
                                variant,
                                index,
                            } => {
                                let field_id = translate_field_id(*index);
                                let variant_id = variant.map(translate_variant_id);
                                match current_ty {
                                    Ty::Adt(TypeId::Adt(type_id), ..) => {
                                        let proj_kind = FieldProjKind::Adt(type_id, variant_id);
                                        ProjectionElem::Field(proj_kind, field_id)
                                    }
                                    Ty::Adt(TypeId::Tuple, generics) => {
                                        assert!(generics.regions.is_empty());
                                        assert!(variant.is_none());
                                        assert!(generics.const_generics.is_empty());
                                        let proj_kind = FieldProjKind::Tuple(generics.types.len());

                                        ProjectionElem::Field(proj_kind, field_id)
                                    }
                                    Ty::Adt(TypeId::Assumed(AssumedTy::Box), generics) => {
                                        assert!(!boxes_are_desugared(self.t_ctx.options.mir_level));

                                        // Some more sanity checks
                                        assert!(generics.regions.is_empty());
                                        assert!(generics.types.len() == 1);
                                        assert!(generics.const_generics.is_empty());
                                        assert!(variant_id.is_none());
                                        assert!(field_id == FieldId::ZERO);

                                        ProjectionElem::DerefBox
                                    }
                                    _ => {
                                        error_or_panic!(self, span, "Unexpected field projection");
                                    }
                                }
                            }
                            ClosureState(index) => {
                                let field_id = translate_field_id(*index);
                                ProjectionElem::Field(FieldProjKind::ClosureState, field_id)
                            }
                        };
                        projection.push(proj_elem);
                    }
                    hax::ProjectionElem::Index(local) => {
                        let local = self.get_local(local).unwrap();
                        let operand = Operand::Copy(Place::new(local));
                        projection.push(ProjectionElem::Index(operand, current_ty));
                    }
                    hax::ProjectionElem::Downcast(..) => {
                        // We view it as a nop (the information from the
                        // downcast has been propagated to the other
                        // projection elements by Hax)
                    }
                    hax::ProjectionElem::ConstantIndex {
                        offset,
                        min_length: _,
                        from_end: false,
                    } => {
                        let ty = Ty::Literal(LiteralTy::Integer(IntegerTy::Usize));
                        let value =
                            RawConstantExpr::Literal(Literal::Scalar(ScalarValue::Usize(*offset)));
                        let offset = Operand::Const(ConstantExpr { value, ty });
                        projection.push(ProjectionElem::Index(offset, current_ty));
                    }
                    hax::ProjectionElem::ConstantIndex { .. } => {
                        // This is not supported yet, see `tests/ui/unsupported/projection-index-from-end.rs`
                        error_or_panic!(self, span, "Unexpected ProjectionElem::ConstantIndex");
                    }
                    hax::ProjectionElem::Subslice { .. } => {
                        // Those don't seem to occur in MIR built
                        error_or_panic!(self, span, "Unexpected ProjectionElem::Subslice");
                    }
                    hax::ProjectionElem::OpaqueCast => {
                        // Don't know what that is
                        error_or_panic!(self, span, "Unexpected ProjectionElem::OpaqueCast");
                    }
                };

                // Return
                Ok((var_id, projection))
            }
        }
    }

    /// Translate an operand with its type
    fn translate_operand_with_type(
        &mut self,
        span: rustc_span::Span,
        operand: &hax::Operand,
    ) -> Result<(Operand, Ty), Error> {
        trace!();
        match operand {
            hax::Operand::Copy(place) => {
                let (p, ty) = self.translate_place_with_type(span, place)?;
                Ok((Operand::Copy(p), ty))
            }
            hax::Operand::Move(place) => {
                let (p, ty) = self.translate_place_with_type(span, place)?;
                Ok((Operand::Move(p), ty))
            }
            hax::Operand::Constant(constant) => {
                let constant = self.translate_constant_to_constant_expr(span, constant)?;
                let ty = constant.ty.clone();
                Ok((Operand::Const(constant), ty))
            }
        }
    }

    /// Translate an operand
    fn translate_operand(
        &mut self,
        span: rustc_span::Span,
        operand: &hax::Operand,
    ) -> Result<Operand, Error> {
        trace!();
        Ok(self.translate_operand_with_type(span, operand)?.0)
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
    fn translate_move_box_first_projector_operand(
        &mut self,
        span: rustc_span::Span,
        operand: &hax::Operand,
    ) -> Result<Operand, Error> {
        trace!();
        match operand {
            hax::Operand::Move(place) => {
                let place = self.translate_place(span, place)?;

                // Sanity check
                let var = self.get_var_from_id(place.var_id).unwrap();
                assert!(var.ty.is_box());

                Ok(Operand::Move(place))
            }
            _ => {
                unreachable!();
            }
        }
    }

    /// Translate an rvalue
    fn translate_rvalue(
        &mut self,
        span: rustc_span::Span,
        rvalue: &hax::Rvalue,
    ) -> Result<Rvalue, Error> {
        let erase_regions = true;
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
            hax::Rvalue::ThreadLocalRef(_) => {
                error_or_panic!(self, span, "Unsupported rvalue: thread local ref");
            }
            hax::Rvalue::AddressOf(_, _) => {
                error_or_panic!(self, span, "Unsupported rvalue: address of");
            }
            hax::Rvalue::Len(place) => {
                let (place, ty) = self.translate_place_with_type(span, place)?;
                let cg = match &ty {
                    Ty::Adt(
                        TypeId::Assumed(aty @ (AssumedTy::Array | AssumedTy::Slice)),
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
                // Put aside the pointer casts (which we don't support), I think
                // casts should only be from integers/booleans to integer/booleans.

                // Translate the target type
                let tgt_ty = self.translate_ty(span, erase_regions, tgt_ty)?;

                // Translate the operand
                let (operand, src_ty) = self.translate_operand_with_type(span, operand)?;

                match (cast_kind, &src_ty, &tgt_ty) {
                    (hax::CastKind::IntToInt, _, _) => {
                        // Note that bool is considered as an integer by Rust.
                        let tgt_ty = *tgt_ty.as_literal();
                        let src_ty = *src_ty.as_literal();

                        Ok(Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::Scalar(src_ty, tgt_ty)),
                            operand,
                        ))
                    }
                    (
                        hax::CastKind::PointerCoercion(hax::PointerCoercion::Unsize),
                        Ty::Ref(
                            _,
                            deref!(Ty::Adt(TypeId::Assumed(AssumedTy::Array), generics)),
                            kind1,
                        ),
                        Ty::Ref(
                            _,
                            deref!(Ty::Adt(TypeId::Assumed(AssumedTy::Slice), generics1)),
                            kind2,
                        ),
                    ) => {
                        // In MIR terminology, we go from &[T; l] to &[T] which means we
                        // effectively "unsize" the type, as `l` no longer appears in the
                        // destination type. At runtime, the converse happens: the length
                        // materializes into the fat pointer.
                        assert!(generics.types.len() == 1 && generics.const_generics.len() == 1);
                        assert!(generics.types[0] == generics1.types[0]);
                        assert!(kind1 == kind2);
                        Ok(Rvalue::UnaryOp(
                            UnOp::ArrayToSlice(
                                *kind1,
                                generics.types[0].clone(),
                                generics.const_generics[0].clone(),
                            ),
                            operand,
                        ))
                    }
                    (hax::CastKind::PointerCoercion(hax::PointerCoercion::Unsize), _, _) => {
                        Ok(Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::Unsize(src_ty.clone(), tgt_ty.clone())),
                            operand,
                        ))
                    }
                    (
                        hax::CastKind::PointerCoercion(hax::PointerCoercion::ClosureFnPointer(
                            safety,
                        )),
                        src_ty @ Ty::Arrow(..),
                        tgt_ty @ Ty::Arrow(..),
                    ) => {
                        assert!(*safety == hax::Safety::Safe);
                        let src_ty = src_ty.clone();
                        let tgt_ty = tgt_ty.clone();
                        Ok(Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::FnPtr(src_ty, tgt_ty)),
                            operand,
                        ))
                    }
                    (
                        hax::CastKind::PointerCoercion(hax::PointerCoercion::ReifyFnPointer),
                        src_ty @ Ty::Arrow(..),
                        tgt_ty @ Ty::Arrow(..),
                    ) => {
                        let src_ty = src_ty.clone();
                        let tgt_ty = tgt_ty.clone();
                        Ok(Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::FnPtr(src_ty, tgt_ty)),
                            operand,
                        ))
                    }
                    _ => {
                        error_or_panic!(
                            self,
                            span,
                            format!(
                                "Unsupported cast:\n\n- rvalue: {:?}\n\n- src={:?}\n\n- dst={:?}",
                                rvalue, src_ty, tgt_ty
                            )
                        )
                    }
                }
            }
            hax::Rvalue::BinaryOp(binop, (left, right)) => Ok(Rvalue::BinaryOp(
                self.t_ctx.translate_binaryop_kind(span, *binop)?,
                self.translate_operand(span, left)?,
                self.translate_operand(span, right)?,
            )),
            hax::Rvalue::NullaryOp(nullop, _ty) => {
                trace!("NullOp: {:?}", nullop);
                // Nullary operations are very low-level and shouldn't be necessary
                // unless one needs to write unsafe code.
                error_or_panic!(self, span, "Nullary operations are not supported");
            }
            hax::Rvalue::UnaryOp(unop, operand) => Ok(Rvalue::UnaryOp(
                translate_unaryop_kind(*unop),
                self.translate_operand(span, operand)?,
            )),
            hax::Rvalue::Discriminant(place) => {
                let (place, ty) = self.translate_place_with_type(span, place)?;
                if let Ty::Adt(TypeId::Adt(adt_id), _) = &ty {
                    Ok(Rvalue::Discriminant(place, *adt_id))
                } else {
                    error_or_panic!(
                        self,
                        span,
                        format!(
                            "Unexpected scrutinee type for ReadDiscriminant: {}",
                            ty.fmt_with_ctx(&self.into_fmt())
                        )
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
                        let t_ty = self.translate_ty(span, erase_regions, ty)?;
                        let cg = ConstGeneric::Value(Literal::Scalar(ScalarValue::Usize(
                            operands_t.len() as u64,
                        )));
                        Ok(Rvalue::Aggregate(
                            AggregateKind::Array(t_ty, cg),
                            operands_t,
                        ))
                    }
                    hax::AggregateKind::Tuple => Ok(Rvalue::Aggregate(
                        AggregateKind::Adt(TypeId::Tuple, None, GenericArgs::empty()),
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
                        // The union field index if specified. We don't handle unions today.
                        error_assert!(self, span, field_index.is_none());

                        // Translate the substitution
                        let generics = self.translate_substs_and_trait_refs(
                            span,
                            erase_regions,
                            None,
                            substs,
                            trait_refs,
                        )?;

                        let type_id = self.translate_type_id(span, adt_id)?;
                        // Sanity check
                        matches!(&type_id, TypeId::Adt(_));

                        use hax::AdtKind;
                        let variant_id = match kind {
                            AdtKind::Struct => None,
                            AdtKind::Enum => {
                                let variant_id = translate_variant_id(*variant_idx);
                                Some(variant_id)
                            }
                            AdtKind::Union => {
                                error_or_panic!(self, span, "Union values are not supported");
                            }
                        };

                        let akind = AggregateKind::Adt(type_id, variant_id, generics);
                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    hax::AggregateKind::Closure(def_id, substs, trait_refs, sig) => {
                        trace!("Closure:\n\n- def_id: {:?}\n\n- sig:\n{:?}", def_id, sig);

                        // Translate the substitution
                        let generics = self.translate_substs_and_trait_refs(
                            span,
                            erase_regions,
                            None,
                            substs,
                            trait_refs,
                        )?;

                        let def_id = self.register_fun_decl_id(span, DefId::from(def_id));
                        let akind = AggregateKind::Closure(def_id, generics);

                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    hax::AggregateKind::RawPtr(..) => {
                        error_or_panic!(self, span, "Raw pointers are not supported");
                    }
                    hax::AggregateKind::Coroutine(..)
                    | hax::AggregateKind::CoroutineClosure(..) => {
                        error_or_panic!(self, span, "Coroutines are not supported");
                    }
                }
            }
            hax::Rvalue::ShallowInitBox(_, _) => {
                error_or_panic!(self, span, "Unsupported rvalue: shallow init box");
            }
        }
    }

    /// Auxiliary function to translate function calls and references to functions.
    /// Translate a function id applied with some substitutions and some optional
    /// arguments.
    ///
    /// We use a special function because the function might be assumed, and
    /// some parameters/arguments might need to be filtered.
    /// We return the fun id, its generics, and filtering information for the
    /// arguments.
    ///
    /// TODO: should we always erase the regions?
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn translate_fun_decl_id_with_args(
        &mut self,
        span: rustc_span::Span,
        erase_regions: bool,
        def_id: &hax::DefId,
        substs: &Vec<hax::GenericArg>,
        args: Option<&Vec<hax::Spanned<hax::Operand>>>,
        trait_refs: &Vec<hax::ImplExpr>,
        trait_info: &Option<hax::ImplExpr>,
    ) -> Result<SubstFunIdOrPanic, Error> {
        let rust_id = DefId::from(def_id);
        let name = self.t_ctx.hax_def_id_to_name(def_id)?;
        let is_local = rust_id.is_local();

        let builtin_fun = BuiltinFun::parse_name(&name);
        if matches!(builtin_fun, Some(BuiltinFun::Panic)) {
            return Ok(SubstFunIdOrPanic::Panic(name));
        }

        // There is something annoying: when going to MIR, the rust compiler
        // sometimes introduces very low-level functions, which we need to
        // catch early - in particular, before we start translating types and
        // arguments, because we won't be able to translate some of them.
        let sfid = if matches!(builtin_fun, Some(BuiltinFun::BoxFree)) {
            assert!(!is_local);

            // This deallocates a box.
            // It should have two type parameters:
            // - the type of the boxed value
            // - the type of a global allocator (which we ignore)
            assert!(substs.len() == 2);
            assert!(trait_refs.is_empty());

            // Translate the type parameter
            let t_ty = if let hax::GenericArg::Type(ty) = substs.get(0).unwrap() {
                self.translate_ty(span, erase_regions, ty)?
            } else {
                unreachable!()
            };

            let args = args
                .map(|args| {
                    assert!(args.len() == 2);
                    // Translate the first argument - note that we use a special
                    // function to translate it: the operand should be of the form:
                    // `move b.0`, and if it is the case it will return `move b`
                    let arg = &args[0].node;
                    let t_arg = self.translate_move_box_first_projector_operand(span, arg)?;
                    Ok(vec![t_arg])
                })
                .transpose()?;

            // Return
            let func = FnPtr {
                func: FunIdOrTraitMethodRef::mk_assumed(AssumedFunId::BoxFree),
                generics: GenericArgs::new_from_types(vec![t_ty]),
            };
            SubstFunId { func, args }
        } else {
            // Retrieve the lists of used parameters, in case of non-local
            // definitions
            let (used_type_args, used_args) = if let Some(builtin_fun) = builtin_fun {
                builtin_fun
                    .to_fun_info()
                    .map(|used| (used.used_type_params, used.used_args))
            } else {
                None
            }
            .unzip();

            // Translate the type parameters
            let generics = self.translate_substs_and_trait_refs(
                span,
                erase_regions,
                used_type_args,
                substs,
                trait_refs,
            )?;

            // Translate the arguments
            let args = args
                .map(|args| self.translate_arguments(span, used_args, args))
                .transpose()?;

            // Trait information
            trace!(
                "Trait information:\n- def_id: {:?}\n- impl source:\n{:?}",
                rust_id,
                trait_info
            );
            trace!(
                "Method traits:\n- def_id: {:?}\n- traits:\n{:?}",
                rust_id,
                trait_refs
            );

            // Check if the function is considered primitive: primitive
            // functions benefit from special treatment.
            let func = if let Some(builtin_fun) = builtin_fun {
                // Primitive function.
                //
                // Note that there are subtleties with regards to the way types parameters
                // are translated, because some functions are actually traits, where the
                // types are used for the resolution. For instance, the following:
                // `core::ops::deref::Deref::<alloc::boxed::Box<T>>::deref`
                // is translated to:
                // `box_deref<T>`
                // (the type parameter is not `Box<T>` but `T`).
                assert!(trait_info.is_none());

                let aid = builtin_fun.to_ullbc_builtin_fun();

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
                    AssumedFunId::BoxNew => {
                        // Nothing to do
                    }
                    AssumedFunId::BoxFree => {
                        // Special case handled elsewhere
                        unreachable!();
                    }
                    AssumedFunId::ArrayIndexShared
                    | AssumedFunId::ArrayIndexMut
                    | AssumedFunId::ArrayToSliceShared
                    | AssumedFunId::ArrayToSliceMut
                    | AssumedFunId::ArrayRepeat
                    | AssumedFunId::SliceIndexShared
                    | AssumedFunId::SliceIndexMut => {
                        // Those cases are introduced later, in micro-passes, by desugaring
                        // projections (for ArrayIndex and ArrayIndexMut for instnace) and=
                        // operations (for ArrayToSlice for instance) to function calls.
                        unreachable!()
                    }
                };

                FunIdOrTraitMethodRef::Fun(FunId::Assumed(aid))
            } else {
                // Two cases depending on whether we call a trait method or not
                match trait_info {
                    None => {
                        // "Regular" function call
                        let def_id = self.register_fun_decl_id(span, rust_id);
                        FunIdOrTraitMethodRef::Fun(FunId::Regular(def_id))
                    }
                    Some(trait_info) => {
                        // Trait method
                        let rust_id = DefId::from(def_id);
                        let impl_expr =
                            self.translate_trait_impl_expr(span, erase_regions, trait_info)?;
                        // The impl source should be Some(...): trait markers (that we may
                        // eliminate) don't have methods.
                        let impl_expr = impl_expr.unwrap();

                        trace!("{:?}", rust_id);

                        let trait_method_fun_id = self.register_fun_decl_id(span, rust_id);
                        let method_name = self.t_ctx.translate_trait_item_name(rust_id)?;

                        FunIdOrTraitMethodRef::Trait(impl_expr, method_name, trait_method_fun_id)
                    }
                }
            };
            SubstFunId {
                func: FnPtr { func, generics },
                args,
            }
        };
        Ok(SubstFunIdOrPanic::Fun(sfid))
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
        let span = statement.source_info.span.rust_span_data.unwrap().span();

        use hax::StatementKind;
        let t_statement: Option<RawStatement> = match &*statement.kind {
            StatementKind::Assign((place, rvalue)) => {
                let t_place = self.translate_place(span, place)?;
                let t_rvalue = self.translate_rvalue(
                    statement.source_info.span.rust_span_data.unwrap().span(),
                    rvalue,
                )?;

                Some(RawStatement::Assign(t_place, t_rvalue))
            }
            StatementKind::FakeRead((_read_cause, place)) => {
                let t_place = self.translate_place(span, place)?;

                Some(RawStatement::FakeRead(t_place))
            }
            StatementKind::PlaceMention(place) => {
                // Simply accesses a place. Introduced for instance in place
                // of `let _ = ...`. We desugar it to a fake read.
                let t_place = self.translate_place(span, place)?;

                Some(RawStatement::FakeRead(t_place))
            }
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                let t_place = self.translate_place(span, place)?;
                let variant_id = translate_variant_id(*variant_index);
                Some(RawStatement::SetDiscriminant(t_place, variant_id))
            }
            StatementKind::StorageLive(_) => {
                // We ignore StorageLive
                None
            }
            StatementKind::StorageDead(local) => {
                let var_id = self.get_local(local).unwrap();
                Some(RawStatement::StorageDead(var_id))
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
                error_or_panic!(self, span, "Unsupported statement kind: coverage");
            }
            StatementKind::Nop => {
                // We ignore this statement
                None
            }
            StatementKind::Deinit(place) => {
                let t_place = self.translate_place(span, place)?;
                Some(RawStatement::Deinit(t_place))
            }
            StatementKind::Intrinsic(_) => {
                error_or_panic!(self, span, "Unsupported statement kind: intrinsic");
            }
            StatementKind::ConstEvalCounter => {
                // See the doc: only used in the interpreter, to check that
                // const code doesn't run for too long or even indefinitely.
                // We consider it as a no-op.
                None
            }
        };

        // Add the span information
        match t_statement {
            None => Ok(None),
            Some(t_statement) => {
                let span = self
                    .t_ctx
                    .translate_span_from_source_info(&body.source_scopes, &statement.source_info);

                Ok(Some(Statement::new(span, t_statement)))
            }
        }
    }

    /// Translate a terminator
    fn translate_terminator(
        &mut self,
        body: &hax::MirBody<()>,
        terminator: &hax::Terminator,
    ) -> Result<Terminator, Error> {
        trace!("About to translate terminator (MIR) {:?}", terminator);
        let rustc_span = terminator.source_info.span.rust_span_data.unwrap().span();

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
            TerminatorKind::SwitchInt { discr, targets } => {
                // Translate the operand which gives the discriminant
                let (discr, discr_ty) = self.translate_operand_with_type(rustc_span, discr)?;

                // Translate the switch targets
                let targets = self.translate_switch_targets(&discr_ty, targets)?;

                RawTerminator::Switch { discr, targets }
            }
            TerminatorKind::UnwindResume => {
                // This is used to correctly unwind. We shouldn't get there: if
                // we panic, the state gets stuck.
                error_or_panic!(self, rustc_span, "Unexpected terminator: UnwindResume");
            }
            TerminatorKind::UnwindTerminate { .. } => {
                error_or_panic!(self, rustc_span, "Unexpected terminator: UnwindTerminate")
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
            } => RawTerminator::Drop {
                place: self.translate_place(rustc_span, place)?,
                target: self.translate_basic_block_id(*target),
            },
            TerminatorKind::Call {
                fun,
                generics,
                args,
                destination,
                target,
                trait_refs,
                trait_info,
                unwind: _, // We consider that panic is an error, and don't model unwinding
                call_source: _,
                fn_span: _,
            } => self.translate_function_call(
                rustc_span,
                fun,
                generics,
                args,
                destination,
                target,
                trait_refs,
                trait_info,
            )?,
            TerminatorKind::Assert {
                cond,
                expected,
                msg: _,
                target,
                unwind: _, // We consider that panic is an error, and don't model unwinding
            } => {
                let cond = self.translate_operand(rustc_span, cond)?;
                let target = self.translate_basic_block_id(*target);
                RawTerminator::Assert {
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
                error_or_panic!(self, rustc_span, "Unsupported terminator: yield");
            }
            TerminatorKind::CoroutineDrop => {
                error_or_panic!(self, rustc_span, "Unsupported terminator: coroutine drop");
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
                error_or_panic!(self, rustc_span, "Inline assembly is not supported");
            }
        };

        // Add the span information
        Ok(Terminator::new(span, t_terminator))
    }

    /// Translate switch targets
    fn translate_switch_targets(
        &mut self,
        switch_ty: &Ty,
        targets: &hax::SwitchTargets,
    ) -> Result<SwitchTargets, Error> {
        trace!("targets: {:?}", targets);
        match targets {
            hax::SwitchTargets::If(if_block, then_block) => {
                let if_block = self.translate_basic_block_id(*if_block);
                let then_block = self.translate_basic_block_id(*then_block);
                Ok(SwitchTargets::If(if_block, then_block))
            }
            hax::SwitchTargets::SwitchInt(_, targets_map, otherwise) => {
                let int_ty = *switch_ty.as_literal().as_integer();
                let targets_map: Vec<(ScalarValue, BlockId)> = targets_map
                    .iter()
                    .map(|(v, tgt)| {
                        let v = ScalarValue::from_le_bytes(int_ty, v.data_le_bytes);
                        let tgt = self.translate_basic_block_id(*tgt);
                        Ok((v, tgt))
                    })
                    .try_collect()?;
                let otherwise = self.translate_basic_block_id(*otherwise);
                Ok(SwitchTargets::SwitchInt(int_ty, targets_map, otherwise))
            }
        }
    }

    /// Translate a function call statement.
    /// Note that `body` is the body of the function being translated, not of the
    /// function referenced in the function call: we need it in order to translate
    /// the blocks we go to after the function call returns.
    #[allow(clippy::too_many_arguments)]
    fn translate_function_call(
        &mut self,
        span: rustc_span::Span,
        fun: &hax::FunOperand,
        generics: &Vec<hax::GenericArg>,
        args: &Vec<hax::Spanned<hax::Operand>>,
        destination: &hax::Place,
        target: &Option<hax::BasicBlock>,
        trait_refs: &Vec<hax::ImplExpr>,
        trait_info: &Option<hax::ImplExpr>,
    ) -> Result<RawTerminator, Error> {
        trace!();
        // There are two cases, depending on whether this is a "regular"
        // call to a top-level function identified by its id, or if we
        // are using a local function pointer (i.e., the operand is a "move").
        match fun {
            hax::FunOperand::Id(def_id) => {
                // Regular function call
                let rust_id = DefId::from(def_id);

                // Translate the function operand - should be a constant: we don't
                // support closures for now
                trace!("func: {:?}", rust_id);

                // Translate the function id, with its parameters
                let erase_regions = true;
                let fid = self.translate_fun_decl_id_with_args(
                    span,
                    erase_regions,
                    def_id,
                    generics,
                    Some(args),
                    trait_refs,
                    trait_info,
                )?;

                match fid {
                    SubstFunIdOrPanic::Panic(name) => {
                        // If the call is `panic!`, then the target is `None`.
                        // I don't know in which other cases it can be `None`.
                        assert!(target.is_none());

                        // We ignore the arguments
                        Ok(RawTerminator::Abort(AbortKind::Panic(name)))
                    }
                    SubstFunIdOrPanic::Fun(fid) => {
                        let lval = self.translate_place(span, destination)?;
                        let next_block = target.map(|target| self.translate_basic_block_id(target));

                        let call = Call {
                            func: FnOperand::Regular(fid.func),
                            args: fid.args.unwrap(),
                            dest: lval,
                        };

                        Ok(RawTerminator::Call {
                            call,
                            target: next_block,
                        })
                    }
                }
            }
            hax::FunOperand::Move(p) => {
                // Call to a local function pointer
                // The function
                let p = self.translate_place(span, p)?;

                let lval = self.translate_place(span, destination)?;
                let next_block = target.map(|target| self.translate_basic_block_id(target));

                // TODO: we may have a problem here because as we don't
                // know which function is being called, we may not be
                // able to filter the arguments properly... But maybe
                // this is rather an issue for the statement which creates
                // the function pointer, by refering to a top-level function
                // for instance.
                let args = self.translate_arguments(span, None, args)?;
                let call = Call {
                    func: FnOperand::Move(p),
                    args,
                    dest: lval,
                };
                Ok(RawTerminator::Call {
                    call,
                    target: next_block,
                })
            }
        }
    }

    /// Evaluate function arguments in a context, and return the list of computed
    /// values.
    fn translate_arguments(
        &mut self,
        span: rustc_span::Span,
        used_args: Option<Vec<bool>>,
        args: &Vec<hax::Spanned<hax::Operand>>,
    ) -> Result<Vec<Operand>, Error> {
        let unspanned_args = args.iter().map(|x| &x.node);
        let args: Vec<&hax::Operand> = match used_args {
            None => unspanned_args.collect(),
            Some(used_args) => {
                assert!(args.len() == used_args.len());
                unspanned_args
                    .zip(used_args.into_iter())
                    .filter_map(|(param, used)| if used { Some(param) } else { None })
                    .collect()
            }
        };

        let mut t_args: Vec<Operand> = Vec::new();
        for arg in args {
            // Translate
            let op = self.translate_operand(span, arg)?;
            t_args.push(op);
        }

        Ok(t_args)
    }

    /// Translate a function body if we can (it has MIR) and we want to (we don't translate bodies
    /// declared opaque, and only translate non-local bodies if `extract_opaque_bodies` is set).
    fn translate_body(
        mut self,
        rust_id: DefId,
        arg_count: usize,
        item_meta: &ItemMeta,
    ) -> Result<Result<Body, Opaque>, Error> {
        // Stopgap measure because there are still many panics in charon and hax.
        let mut this = panic::AssertUnwindSafe(&mut self);
        let res =
            panic::catch_unwind(move || this.translate_body_aux(rust_id, arg_count, item_meta));
        match res {
            Ok(Ok(body)) => Ok(body),
            // Translation error
            Ok(Err(e)) => Err(e),
            Err(_) => {
                let span = item_meta.span.rust_span();
                error_or_panic!(self, span, "Thread panicked when extracting body.");
            }
        }
    }

    fn translate_body_aux(
        &mut self,
        rust_id: DefId,
        arg_count: usize,
        item_meta: &ItemMeta,
    ) -> Result<Result<Body, Opaque>, Error> {
        let tcx = self.t_ctx.tcx;

        if item_meta.opacity.with_private_contents().is_opaque() {
            // The bodies of foreign functions are opaque by default.
            return Ok(Err(Opaque));
        }

        // Retrieve the body
        let Some(body) = get_mir_for_def_id_and_level(tcx, rust_id, self.t_ctx.options.mir_level)
        else {
            return Ok(Err(Opaque));
        };

        // Here, we have to create a MIR state, which contains the body
        // Yes, we have to clone, this is annoying: we end up cloning the body twice
        let state = self
            .hax_state
            .clone()
            .with_owner_id(rust_id)
            .with_mir(Rc::new(body.clone()));
        // Translate
        let body: hax::MirBody<()> = body.sinto(&state);

        // Initialize the local variables
        trace!("Translating the body locals");
        self.translate_body_locals(&body)?;

        // Translate the expression body
        trace!("Translating the expression body");
        self.translate_transparent_expression_body(&body)?;

        // Compute the span information
        let span = self.translate_span_from_rspan(body.span);

        // We need to convert the blocks map to an index vector
        // We clone things while we could move them...
        let mut blocks = Vector::new();
        for (id, block) in mem::take(&mut self.blocks) {
            let new_id = blocks.push(block);
            // Sanity check to make sure we don't mess with the indices
            assert!(id == new_id);
        }

        // Create the body
        Ok(Ok(Body::Unstructured(ExprBody {
            span,
            arg_count,
            locals: mem::take(&mut self.vars),
            body: blocks,
        })))
    }

    /// Translate a function's signature, and initialize a body translation context
    /// at the same time - the function signature gives us the list of region and
    /// type parameters, that we put in the translation context.
    fn translate_function_signature(
        &mut self,
        def_id: DefId,
        item_meta: &ItemMeta,
        def: &hax::Def,
    ) -> Result<FunSig, Error> {
        let tcx = self.t_ctx.tcx;
        let erase_regions = false;
        let span = item_meta.span.rust_span();

        let signature = match def {
            hax::Def::Closure { args, .. } => &args.sig,
            hax::Def::Fn { sig, .. } => sig,
            hax::Def::AssocFn { sig, .. } => sig,
            _ => panic!("Unexpected definition for function: {def:?}"),
        };

        // Some debugging information:
        trace!("Def id: {def_id:?}:\n\n- generics:\n{:?}\n\n- signature bound vars:\n{:?}\n\n- signature:\n{:?}\n",
               tcx.generics_of(def_id), signature.bound_vars, signature);

        // The parameters (and in particular the lifetimes) are split between
        // early bound and late bound parameters. See those blog posts for explanations:
        // https://smallcultfollowing.com/babysteps/blog/2013/10/29/intermingled-parameter-lists/
        // https://smallcultfollowing.com/babysteps/blog/2013/11/04/intermingled-parameter-lists/
        // Note that only lifetimes can be late bound.
        //
        // [TyCtxt.generics_of] gives us the early-bound parameters
        // The late-bounds parameters are bound in the [Binder] returned by
        // [TyCtxt.type_of].

        // Add the early bound parameters and predicates.
        self.push_generics_for_def(span, def_id, &def)?;

        // Add the *late-bound* parameters (bound in the signature, can only be lifetimes).
        let bvar_names = signature
            .bound_vars
            .iter()
            // There should only be regions in the late-bound parameters
            .map(|bvar| match bvar {
                hax::BoundVariableKind::Region(br) => Ok(translate_bound_region_kind_name(&br)),
                hax::BoundVariableKind::Ty(_) | hax::BoundVariableKind::Const => {
                    error_or_panic!(self, span, format!("Unexpected bound variable: {:?}", bvar))
                }
            })
            .try_collect()?;
        self.set_first_bound_regions_group(bvar_names);

        let generics = self.get_generics();

        // Translate the signature
        trace!("signature of {def_id:?}:\n{:?}", signature.value);
        let inputs: Vec<Ty> = signature
            .value
            .inputs
            .iter()
            .map(|ty| self.translate_ty(span, erase_regions, ty))
            .try_collect()?;
        let output = self.translate_ty(span, erase_regions, &signature.value.output)?;

        let fmt_ctx = self.into_fmt();
        trace!(
            "# Input variables types:\n{}",
            iterator_to_string(&|x| fmt_ctx.format_object(x), inputs.iter())
        );
        trace!(
            "# Output variable type:\n{}",
            fmt_ctx.format_object(&output)
        );

        let is_unsafe = match signature.value.safety {
            hax::Safety::Unsafe => true,
            hax::Safety::Safe => false,
        };

        let closure_info = match def {
            hax::Def::Closure { args, .. } => {
                let kind = match args.kind {
                    hax::ClosureKind::Fn => ClosureKind::Fn,
                    hax::ClosureKind::FnMut => ClosureKind::FnMut,
                    hax::ClosureKind::FnOnce => ClosureKind::FnOnce,
                };
                let state = args
                    .upvar_tys
                    .iter()
                    .map(|ty| self.translate_ty(span, erase_regions, &ty))
                    .try_collect::<Vec<Ty>>()?;
                Some(ClosureInfo { kind, state })
            }
            hax::Def::Fn { .. } => None,
            hax::Def::AssocFn { .. } => None,
            _ => panic!("Unexpected definition for function: {def:?}"),
        };

        let parent_params_info = match def {
            hax::Def::AssocFn {
                parent,
                associated_item,
                ..
            } => {
                let parent_def = self.t_ctx.hax_def(parent.into());
                let (parent_generics, parent_predicates) = parent_def.generics().unwrap();
                let mut params_info = self.count_generics(parent_generics, parent_predicates)?;
                // If this is a trait decl method, we need to adjust the number of parent clauses
                if matches!(
                    associated_item.container,
                    hax::AssocItemContainer::TraitContainer { .. }
                ) {
                    // All the trait clauses are registered as parent (of Self) trait clauses, not
                    // as local trait clauses.
                    params_info.num_trait_clauses = 0;
                }
                Some(params_info)
            }
            _ => None,
        };

        Ok(FunSig {
            generics,
            is_unsafe,
            is_closure: matches!(def, hax::Def::Closure { .. }),
            closure_info,
            parent_params_info,
            inputs,
            output,
        })
    }
}

impl<'tcx, 'ctx> TranslateCtx<'tcx, 'ctx> {
    /// Translate one function.
    pub fn translate_function(
        &mut self,
        def_id: FunDeclId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::Def,
    ) -> Result<FunDecl, Error> {
        trace!("About to translate function:\n{:?}", rust_id);
        let def_span = item_meta.span.rust_span();

        // Initialize the body translation context
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        // Check whether this function is a method declaration for a trait definition.
        // If this is the case, it shouldn't contain a body.
        let kind = bt_ctx
            .t_ctx
            .get_item_kind(&DepSource::make(rust_id, def_span), def)?;
        let is_trait_method_decl = match &kind {
            ItemKind::Regular
            | ItemKind::TraitItemImpl { .. }
            | ItemKind::TraitItemProvided(..) => false,
            ItemKind::TraitItemDecl(..) => true,
        };

        // Translate the function signature
        trace!("Translating function signature");
        let signature = bt_ctx.translate_function_signature(rust_id, &item_meta, def)?;

        let body_id = if !is_trait_method_decl {
            // Translate the body. This doesn't store anything if we can't/decide not to translate
            // this body.
            match bt_ctx.translate_body(rust_id, signature.inputs.len(), &item_meta) {
                Ok(Ok(body)) => Ok(self.translated.bodies.push(body)),
                // Opaque declaration
                Ok(Err(Opaque)) => Err(Opaque),
                // Translation error. We reserve a slot and leave it empty.
                // FIXME: handle error cases more explicitly.
                Err(_) => Ok(self.translated.bodies.reserve_slot()),
            }
        } else {
            Err(Opaque)
        };

        Ok(FunDecl {
            def_id,
            rust_id,
            item_meta,
            signature,
            kind,
            body: body_id,
        })
    }

    /// Translate one global.
    pub fn translate_global(
        &mut self,
        def_id: GlobalDeclId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::Def,
    ) -> Result<GlobalDecl, Error> {
        trace!("About to translate global:\n{:?}", rust_id);
        let span = item_meta.span.rust_span();

        // Initialize the body translation context
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        // Retrieve the kind
        let global_kind = bt_ctx
            .t_ctx
            .get_item_kind(&DepSource::make(rust_id, span), &def)?;

        // Translate the generics and predicates - globals *can* have generics
        // Ex.:
        // ```
        // impl<const N : usize> Foo<N> {
        //   const LEN : usize = N;
        // }
        // ```
        bt_ctx.push_generics_for_def(span, rust_id, def)?;
        let generics = bt_ctx.get_generics();

        let hax_state = &bt_ctx.hax_state;

        trace!("Translating global type");
        let mir_ty = bt_ctx.t_ctx.tcx.type_of(rust_id).instantiate_identity();
        let erase_regions = false; // This doesn't matter: there shouldn't be any regions
        let ty = bt_ctx.translate_ty(span, erase_regions, &mir_ty.sinto(hax_state))?;

        // Translate its body like the body of a function. This returns `Opaque if we can't/decide
        // not to translate this body.
        let body_id = match bt_ctx.translate_body(rust_id, 0, &item_meta) {
            Ok(Ok(body)) => Ok(self.translated.bodies.push(body)),
            // Opaque declaration
            Ok(Err(Opaque)) => Err(Opaque),
            // Translation error. We reserve a slot and leave it empty.
            // FIXME: handle error cases more explicitly.
            Err(_) => Ok(self.translated.bodies.reserve_slot()),
        };

        Ok(GlobalDecl {
            def_id,
            rust_id,
            item_meta,
            generics,
            ty,
            kind: global_kind,
            body: body_id,
        })
    }
}
