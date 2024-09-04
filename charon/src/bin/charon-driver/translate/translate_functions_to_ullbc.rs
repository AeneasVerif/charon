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
            hax::MutBorrowKind::ClosureCapture => BorrowKind::UniqueImmutable,
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
        def: &hax::FullDef,
    ) -> Result<ItemKind, Error> {
        let assoc_item = match &def.kind {
            hax::FullDefKind::AssocTy {
                associated_item, ..
            }
            | hax::FullDefKind::AssocConst {
                associated_item, ..
            }
            | hax::FullDefKind::AssocFn {
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
                        overrides_default,
                        ..
                    } => {
                        let trait_id = self.register_trait_decl_id(src, implemented_trait.into());
                        let impl_id = self.register_trait_impl_id(src, impl_id.into());
                        ItemKind::TraitImpl {
                            impl_id,
                            trait_id,
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
                    hax::AssocItemContainer::TraitContainer { trait_id } => {
                        // The trait id should be Some(...): trait markers (that we may eliminate)
                        // don't have associated items.
                        let trait_id = self.register_trait_decl_id(src, trait_id.into());
                        let item_name = TraitItemName(assoc.name.clone());

                        ItemKind::TraitDecl {
                            trait_id,
                            item_name,
                            has_default: assoc.has_value,
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
                            Ty::Ref(_, _, _) | Ty::RawPtr(_, _) => {
                                projection.push(ProjectionElem::Deref);
                            }
                            Ty::Adt(TypeId::Builtin(BuiltinTy::Box), generics) => {
                                // This case only happens in some MIR levels
                                assert!(!boxes_are_desugared(self.t_ctx.options.mir_level));
                                assert!(generics.regions.is_empty());
                                assert!(generics.types.len() == 1);
                                assert!(generics.const_generics.is_empty());
                                projection.push(ProjectionElem::DerefBox);
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
                                    Ty::Adt(TypeId::Builtin(BuiltinTy::Box), generics) => {
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
                        projection.push(ProjectionElem::Index {
                            offset: operand,
                            from_end: false,
                            ty: current_ty,
                        });
                    }
                    hax::ProjectionElem::Downcast(..) => {
                        // We view it as a nop (the information from the
                        // downcast has been propagated to the other
                        // projection elements by Hax)
                    }
                    &hax::ProjectionElem::ConstantIndex {
                        offset,
                        from_end,
                        min_length: _,
                    } => {
                        let offset = Operand::Const(ScalarValue::Usize(offset).to_constant());
                        projection.push(ProjectionElem::Index {
                            offset,
                            from_end,
                            ty: current_ty,
                        });
                    }
                    &hax::ProjectionElem::Subslice { from, to, from_end } => {
                        let from = Operand::Const(ScalarValue::Usize(from).to_constant());
                        let to = Operand::Const(ScalarValue::Usize(to).to_constant());
                        projection.push(ProjectionElem::Subslice {
                            from,
                            to,
                            from_end,
                            ty: current_ty,
                        });
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
                error_or_panic!(
                    self,
                    span,
                    "charon does not support thread local references"
                );
            }
            hax::Rvalue::AddressOf(mtbl, place) => {
                let mtbl = if *mtbl { RefKind::Mut } else { RefKind::Shared };
                let place = self.translate_place(span, place)?;
                Ok(Rvalue::RawPtr(place, mtbl))
            }
            hax::Rvalue::Len(place) => {
                let (place, ty) = self.translate_place_with_type(span, place)?;
                let cg = match &ty {
                    Ty::Adt(
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
                let tgt_ty = self.translate_ty(span, erase_regions, tgt_ty)?;

                // Translate the operand
                let (operand, src_ty) = self.translate_operand_with_type(span, operand)?;

                match cast_kind {
                    hax::CastKind::IntToInt
                    | hax::CastKind::IntToFloat
                    | hax::CastKind::FloatToInt
                    | hax::CastKind::FloatToFloat => {
                        let tgt_ty = *tgt_ty.as_literal();
                        let src_ty = *src_ty.as_literal();
                        Ok(Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::Scalar(src_ty, tgt_ty)),
                            operand,
                        ))
                    }
                    hax::CastKind::PtrToPtr
                    | hax::CastKind::PointerCoercion(hax::PointerCoercion::MutToConstPointer)
                    | hax::CastKind::PointerCoercion(hax::PointerCoercion::ArrayToPointer)
                    | hax::CastKind::FnPtrToPtr
                    | hax::CastKind::PointerExposeProvenance
                    | hax::CastKind::PointerWithExposedProvenance
                    | hax::CastKind::DynStar => Ok(Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::RawPtr(src_ty, tgt_ty)),
                        operand,
                    )),
                    hax::CastKind::PointerCoercion(
                        hax::PointerCoercion::ClosureFnPointer(_)
                        | hax::PointerCoercion::UnsafeFnPointer
                        | hax::PointerCoercion::ReifyFnPointer,
                    ) => Ok(Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::FnPtr(src_ty, tgt_ty)),
                        operand,
                    )),
                    hax::CastKind::Transmute => Ok(Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::Transmute(src_ty, tgt_ty)),
                        operand,
                    )),
                    hax::CastKind::PointerCoercion(hax::PointerCoercion::Unsize) => {
                        let unop = if let (
                            Ty::Ref(
                                _,
                                deref!(Ty::Adt(TypeId::Builtin(BuiltinTy::Array), generics)),
                                kind1,
                            ),
                            Ty::Ref(
                                _,
                                deref!(Ty::Adt(TypeId::Builtin(BuiltinTy::Slice), generics1)),
                                kind2,
                            ),
                        ) = (&src_ty, &tgt_ty)
                        {
                            // In MIR terminology, we go from &[T; l] to &[T] which means we
                            // effectively "unsize" the type, as `l` no longer appears in the
                            // destination type. At runtime, the converse happens: the length
                            // materializes into the fat pointer.
                            assert!(
                                generics.types.len() == 1 && generics.const_generics.len() == 1
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
                self.t_ctx.translate_binaryop_kind(span, *binop)?,
                self.translate_operand(span, left)?,
                self.translate_operand(span, right)?,
            )),
            hax::Rvalue::NullaryOp(nullop, ty) => {
                trace!("NullOp: {:?}", nullop);
                let ty = self.translate_ty(span, erase_regions, ty)?;
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
                };
                Ok(Rvalue::NullaryOp(op, ty))
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
                        AggregateKind::Adt(TypeId::Tuple, None, None, GenericArgs::empty()),
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
                        // TODO: replace with a call to `ptr::from_raw_parts`.
                        error_or_panic!(self, span, "Wide raw pointers are not supported");
                    }
                    hax::AggregateKind::Coroutine(..)
                    | hax::AggregateKind::CoroutineClosure(..) => {
                        error_or_panic!(self, span, "Coroutines are not supported");
                    }
                }
            }
            hax::Rvalue::ShallowInitBox(op, ty) => {
                let op = self.translate_operand(span, op)?;
                let ty = self.translate_ty(span, erase_regions, ty)?;
                Ok(Rvalue::ShallowInitBox(op, ty))
            }
        }
    }

    /// Checks whether the given id corresponds to a built-in function.
    fn recognize_builtin_fun(&mut self, def_id: &hax::DefId) -> Result<Option<BuiltinFun>, Error> {
        use rustc_hir::lang_items::LangItem;
        let tcx = self.t_ctx.tcx;
        let rust_id = DefId::from(def_id);
        let name = self.t_ctx.hax_def_id_to_name(def_id)?;

        let panic_lang_items = &[LangItem::Panic, LangItem::PanicFmt, LangItem::BeginPanic];
        let panic_names = &[&["core", "panicking", "assert_failed"], EXPLICIT_PANIC_NAME];
        if tcx.is_diagnostic_item(rustc_span::sym::box_new, rust_id) {
            Ok(Some(BuiltinFun::BoxNew))
        } else if panic_lang_items
            .iter()
            .any(|i| tcx.is_lang_item(rust_id, *i))
            || panic_names.iter().any(|panic| name.equals_ref_name(panic))
        {
            Ok(Some(BuiltinFun::Panic))
        } else {
            Ok(None)
        }
    }

    /// Auxiliary function to translate function calls and references to functions.
    /// Translate a function id applied with some substitutions and some optional
    /// arguments.
    ///
    /// We use a special function because the function might be built-in, and
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
        let builtin_fun = self.recognize_builtin_fun(def_id)?;
        if matches!(builtin_fun, Some(BuiltinFun::Panic)) {
            let name = self.t_ctx.hax_def_id_to_name(def_id)?;
            return Ok(SubstFunIdOrPanic::Panic(name));
        }

        // Translate the type parameters
        let generics =
            self.translate_substs_and_trait_refs(span, erase_regions, None, substs, trait_refs)?;

        // Translate the arguments
        let args = args
            .map(|args| self.translate_arguments(span, args))
            .transpose()?;

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
                BuiltinFunId::BoxNew => {
                    // Nothing to do
                }
                BuiltinFunId::Index { .. }
                | BuiltinFunId::ArrayToSliceShared
                | BuiltinFunId::ArrayToSliceMut
                | BuiltinFunId::ArrayRepeat => {
                    // Those cases are introduced later, in micro-passes, by desugaring
                    // projections (for ArrayIndex and ArrayIndexMut for instnace) and=
                    // operations (for ArrayToSlice for instance) to function calls.
                    unreachable!()
                }
            };

            FunIdOrTraitMethodRef::Fun(FunId::Builtin(aid))
        } else {
            let rust_id = DefId::from(def_id);
            let fun_id = self.register_fun_decl_id(span, rust_id);
            // Two cases depending on whether we call a trait method or not
            match trait_info {
                None => {
                    // "Regular" function call
                    FunIdOrTraitMethodRef::Fun(FunId::Regular(fun_id))
                }
                Some(trait_info) => {
                    // Trait method
                    let impl_expr =
                        self.translate_trait_impl_expr(span, erase_regions, trait_info)?;
                    // The impl source should be Some(...): trait markers (that we may
                    // eliminate) don't have methods.
                    let impl_expr = impl_expr.unwrap();

                    let method_name = self.t_ctx.translate_trait_item_name(rust_id)?;
                    FunIdOrTraitMethodRef::Trait(impl_expr, method_name, fun_id)
                }
            }
        };
        let sfid = SubstFunId {
            func: FnPtr { func, generics },
            args,
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
                // Simply accesses a place, for use of the borrow checker. Introduced for instance
                // in place of `let _ = ...`. We desugar it to a fake read.
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
            // We ignore StorageLive
            StatementKind::StorageLive(_) => None,
            StatementKind::StorageDead(local) => {
                let var_id = self.get_local(local).unwrap();
                Some(RawStatement::StorageDead(var_id))
            }
            StatementKind::Deinit(place) => {
                let t_place = self.translate_place(span, place)?;
                Some(RawStatement::Deinit(t_place))
            }
            StatementKind::Intrinsic(_) => {
                error_or_panic!(self, span, "Unsupported statement kind: intrinsic");
            }
            // This is for the stacked borrows memory model.
            StatementKind::Retag(_, _) => None,
            // There are user-provided type annotations with no semantic effect (since we get a
            // fully-typechecked MIR (TODO: this isn't quite true with opaque types, we should
            // really use promoted MIR)).
            StatementKind::AscribeUserType(_, _) => None,
            // Used for coverage instrumentation.
            StatementKind::Coverage(_) => None,
            // Used in the interpreter to check that const code doesn't run for too long or even
            // indefinitely.
            StatementKind::ConstEvalCounter => None,
            StatementKind::Nop => None,
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
                    assert: Assert {
                        cond,
                        expected: *expected,
                    },
                    target,
                }
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
            TerminatorKind::CoroutineDrop
            | TerminatorKind::TailCall { .. }
            | TerminatorKind::Yield { .. } => {
                error_or_panic!(
                    self,
                    rustc_span,
                    format!("Unsupported terminator: {:?}", terminator.kind)
                );
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
                let args = self.translate_arguments(span, args)?;
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
        if item_meta.opacity.with_private_contents().is_opaque() {
            // The bodies of foreign functions are opaque by default.
            return Ok(Err(Opaque));
        }

        // Retrieve the body
        let Some(body) =
            get_mir_for_def_id_and_level(self.t_ctx.tcx, rust_id, self.t_ctx.options.mir_level)
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
        let span = self.translate_span_from_hax(body.span);

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
        def: &hax::FullDef,
    ) -> Result<FunSig, Error> {
        let erase_regions = false;
        let span = item_meta.span.rust_span();

        let signature = match &def.kind {
            hax::FullDefKind::Closure { args, .. } => &args.sig,
            hax::FullDefKind::Fn { sig, .. } => sig,
            hax::FullDefKind::AssocFn { sig, .. } => sig,
            _ => panic!("Unexpected definition for function: {def:?}"),
        };

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

        let closure_info = match &def.kind {
            hax::FullDefKind::Closure { args, .. } => {
                let kind = match args.kind {
                    hax::ClosureKind::Fn => ClosureKind::Fn,
                    hax::ClosureKind::FnMut => ClosureKind::FnMut,
                    hax::ClosureKind::FnOnce => ClosureKind::FnOnce,
                };
                let state = args
                    .upvar_tys
                    .iter()
                    .map(|ty| self.translate_ty(span, erase_regions, &ty))
                    .try_collect::<Vector<TypeVarId, Ty>>()?;
                Some(ClosureInfo { kind, state })
            }
            hax::FullDefKind::Fn { .. } => None,
            hax::FullDefKind::AssocFn { .. } => None,
            _ => panic!("Unexpected definition for function: {def:?}"),
        };

        let parent_params_info = match &def.kind {
            hax::FullDefKind::AssocFn {
                parent,
                associated_item,
                ..
            } => {
                let parent_def = self.t_ctx.hax_def(parent);
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
            is_closure: matches!(&def.kind, hax::FullDefKind::Closure { .. }),
            closure_info,
            parent_params_info,
            inputs,
            output,
        })
    }
}

impl<'tcx, 'ctx> TranslateCtx<'tcx, 'ctx> {
    /// Translate one function.
    #[tracing::instrument(skip(self, rust_id, item_meta))]
    pub fn translate_function(
        &mut self,
        def_id: FunDeclId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
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
        let is_trait_method_decl_without_default = match &kind {
            ItemKind::Regular | ItemKind::TraitImpl { .. } => false,
            ItemKind::TraitDecl { has_default, .. } => !has_default,
        };

        // Translate the function signature
        trace!("Translating function signature");
        let signature = bt_ctx.translate_function_signature(rust_id, &item_meta, def)?;

        let body_id = if !is_trait_method_decl_without_default {
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
    #[tracing::instrument(skip(self, rust_id, item_meta))]
    pub fn translate_global(
        &mut self,
        def_id: GlobalDeclId,
        rust_id: DefId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
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

        trace!("Translating global type");
        let ty = match &def.kind {
            hax::FullDefKind::Const { ty, .. }
            | hax::FullDefKind::AssocConst { ty, .. }
            | hax::FullDefKind::Static { ty, .. } => ty,
            _ => panic!("Unexpected def for constant: {def:?}"),
        };
        let erase_regions = false; // This doesn't matter: there shouldn't be any regions
        let ty = bt_ctx.translate_ty(span, erase_regions, ty)?;

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
