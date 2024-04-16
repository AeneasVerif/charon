//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

use crate::assumed;
use crate::common::*;
use crate::expressions::*;
use crate::formatter::{Formatter, IntoFormatter};
use crate::get_mir::{boxes_are_desugared, get_mir_for_def_id_and_level};
use crate::translate_ctx::*;
use crate::translate_types;
use crate::types::*;
use crate::ullbc_ast::*;
use crate::values::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::START_BLOCK;
use rustc_middle::ty;
use translate_types::translate_bound_region_kind_name;

pub(crate) struct SubstFunId {
    pub func: FnPtr,
    pub args: Option<Vec<Operand>>,
}

pub(crate) enum SubstFunIdOrPanic {
    Panic,
    Fun(SubstFunId),
}

fn translate_variant_id(id: hax::VariantIdx) -> VariantId::Id {
    VariantId::Id::new(id)
}

fn translate_field_id(id: hax::FieldIdx) -> FieldId::Id {
    use rustc_index::Idx;
    FieldId::Id::new(id.index())
}

/// Translate a `BorrowKind`
fn translate_borrow_kind(borrow_kind: hax::BorrowKind) -> BorrowKind {
    match borrow_kind {
        hax::BorrowKind::Shared => BorrowKind::Shared,
        hax::BorrowKind::Mut {
            allow_two_phase_borrow,
        } => {
            if allow_two_phase_borrow {
                BorrowKind::TwoPhaseMut
            } else {
                BorrowKind::Mut
            }
        }
        hax::BorrowKind::Unique => {
            unimplemented!();
        }
        hax::BorrowKind::Shallow => BorrowKind::Shallow,
    }
}

fn translate_unaryop_kind(binop: hax::UnOp) -> UnOp {
    match binop {
        hax::UnOp::Not => UnOp::Not,
        hax::UnOp::Neg => UnOp::Neg,
    }
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
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    fn translate_binaryop_kind(
        &mut self,
        span: rustc_span::Span,
        binop: hax::BinOp,
    ) -> Result<BinOp, Error> {
        match binop {
            hax::BinOp::BitXor => Ok(BinOp::BitXor),
            hax::BinOp::BitAnd => Ok(BinOp::BitAnd),
            hax::BinOp::BitOr => Ok(BinOp::BitOr),
            hax::BinOp::Eq => Ok(BinOp::Eq),
            hax::BinOp::Lt => Ok(BinOp::Lt),
            hax::BinOp::Le => Ok(BinOp::Le),
            hax::BinOp::Ne => Ok(BinOp::Ne),
            hax::BinOp::Ge => Ok(BinOp::Ge),
            hax::BinOp::Gt => Ok(BinOp::Gt),
            hax::BinOp::Div => Ok(BinOp::Div),
            hax::BinOp::Rem => Ok(BinOp::Rem),
            hax::BinOp::Add => Ok(BinOp::Add),
            hax::BinOp::Sub => Ok(BinOp::Sub),
            hax::BinOp::Mul => Ok(BinOp::Mul),
            hax::BinOp::Shl => Ok(BinOp::Shl),
            hax::BinOp::Shr => Ok(BinOp::Shr),
            hax::BinOp::Offset => {
                error_or_panic!(self, span, "Unsupported binary operation: offset")
            }
        }
    }

    pub(crate) fn get_item_kind(
        &mut self,
        src: &Option<DepSource>,
        rust_id: DefId,
    ) -> Result<ItemKind, Error> {
        trace!("rust_id: {:?}", rust_id);
        let tcx = self.tcx;
        if let Some(assoc) = tcx.opt_associated_item(rust_id) {
            let kind = match assoc.container {
                ty::AssocItemContainer::ImplContainer => {
                    // This item is defined in an impl block.
                    // It can be a regular item in an impl block or a trait
                    // item implementation.
                    //
                    // Ex.: (with methods)
                    // ====
                    // ```
                    // impl<T> List<T> {
                    //   fn new() -> Self { ... } <- implementation
                    // }
                    //
                    // impl Foo for Bar {
                    //   fn baz(...) { ... } // <- implementation of a trait method
                    // }
                    // ```

                    // Check if there is a trait item (if yes, it is a trait item
                    // implementation, if no it is a regular item).
                    // Remark: this trait item is the id of the item associated
                    // in the trait. For instance:
                    // ```
                    // trait Foo {
                    //   fn bar(); // Id: Foo_bar
                    // }
                    // ```
                    //
                    // impl Foo for List {
                    //   fn bar() { ... } // trait_item_def_id: Some(Foo_bar)
                    // }
                    match assoc.trait_item_def_id {
                        None => ItemKind::Regular,
                        Some(trait_item_id) => {
                            let trait_id = tcx.trait_of_item(trait_item_id).unwrap();
                            let trait_id = self.translate_trait_decl_id(src, trait_id)?;
                            // The trait id should be Some(...): trait markers (that we
                            // may eliminate) don't have methods.
                            let trait_id = trait_id.unwrap();

                            // Retrieve the id of the impl block
                            let impl_id = self
                                .translate_trait_impl_id(
                                    src,
                                    tcx.predicates_of(rust_id).parent.unwrap(),
                                )?
                                .unwrap();

                            let item_name = self.translate_trait_item_name(trait_item_id)?;

                            // Check if the current function implements a provided method.
                            // We do so by retrieving the def id of the method which is
                            // implemented, and checking its kind.
                            let provided = match self.get_item_kind(src, trait_item_id)? {
                                ItemKind::TraitItemDecl(..) => false,
                                ItemKind::TraitItemProvided(..) => true,
                                ItemKind::Regular | ItemKind::TraitItemImpl { .. } => {
                                    unreachable!()
                                }
                            };

                            ItemKind::TraitItemImpl {
                                impl_id,
                                trait_id,
                                item_name,
                                provided,
                            }
                        }
                    }
                }
                ty::AssocItemContainer::TraitContainer => {
                    // This method is the *declaration* of a trait item
                    // Ex.:
                    // ====
                    // ```
                    // trait Foo {
                    //   fn baz(...); // <- declaration of a trait method
                    // }
                    // ```

                    // Yet, this could be a default item implementation, in which
                    // case there is a body: we need to check that.

                    // In order to check if this is a provided item, we check
                    // the defaultness (i.e., whether the item has a default value):
                    let is_provided = tcx.impl_defaultness(rust_id).has_value();

                    // Compute additional information
                    let item_name = self.translate_trait_item_name(rust_id)?;
                    let trait_id = tcx.trait_of_item(rust_id).unwrap();
                    let trait_id = self.translate_trait_decl_id(src, trait_id)?;
                    // The trait id should be Some(...): trait markers (that we
                    // may eliminate) don't have associated items.
                    let trait_id = trait_id.unwrap();

                    if is_provided {
                        ItemKind::TraitItemProvided(trait_id, item_name)
                    } else {
                        ItemKind::TraitItemDecl(trait_id, item_name)
                    }
                }
            };
            Ok(kind)
        } else {
            Ok(ItemKind::Regular)
        }
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
    fn translate_basic_block_id(&mut self, block_id: hax::BasicBlock) -> BlockId::Id {
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
    ) -> Result<(VarId::Id, Projection), Error> {
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
                                assert!(!boxes_are_desugared(self.t_ctx.mir_level));
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
                                        assert!(!boxes_are_desugared(self.t_ctx.mir_level));

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
                        projection.push(ProjectionElem::Index(local, current_ty));
                    }
                    hax::ProjectionElem::Downcast(..) => {
                        // We view it as a nop (the information from the
                        // downcast has been propagated to the other
                        // projection elements by Hax)
                    }
                    hax::ProjectionElem::ConstantIndex { .. }
                    | hax::ProjectionElem::Subslice { .. } => {
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
        use std::ops::Deref;
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
                            Option::Some(generics.const_generics[0].clone())
                        } else {
                            Option::None
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
                let (op, src_ty) = self.translate_operand_with_type(span, operand)?;

                match (cast_kind, &src_ty, &tgt_ty) {
                    (hax::CastKind::IntToInt, _, _) => {
                        // Note that bool is considered as an integer by Rust.
                        let tgt_ty = *tgt_ty.as_literal();
                        let src_ty = *src_ty.as_literal();

                        Ok(Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::Scalar(src_ty, tgt_ty)),
                            op,
                        ))
                    }
                    (
                        hax::CastKind::Pointer(hax::PointerCast::Unsize),
                        Ty::Ref(_, t1, kind1),
                        Ty::Ref(_, t2, kind2),
                    ) => {
                        // In MIR terminology, we go from &[T; l] to &[T] which means we
                        // effectively "unsize" the type, as `l` no longer appears in the
                        // destination type. At runtime, the converse happens: the length
                        // materializes into the fat pointer.
                        match (&**t1, &**t2) {
                            (
                                Ty::Adt(TypeId::Assumed(AssumedTy::Array), generics),
                                Ty::Adt(TypeId::Assumed(AssumedTy::Slice), generics1),
                            ) => {
                                assert!(
                                    generics.types.len() == 1 && generics.const_generics.len() == 1
                                );
                                assert!(generics.types[0] == generics1.types[0]);
                                assert!(kind1 == kind2);
                                Ok(Rvalue::UnaryOp(
                                    UnOp::ArrayToSlice(
                                        *kind1,
                                        generics.types[0].clone(),
                                        generics.const_generics[0].clone(),
                                    ),
                                    op,
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
                    (
                        hax::CastKind::Pointer(hax::PointerCast::ClosureFnPointer(unsafety)),
                        src_ty @ Ty::Arrow(..),
                        tgt_ty @ Ty::Arrow(..),
                    ) => {
                        assert!(*unsafety == hax::Unsafety::Normal);
                        let src_ty = src_ty.clone();
                        let tgt_ty = tgt_ty.clone();
                        Ok(Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::FnPtr(src_ty, tgt_ty)),
                            op,
                        ))
                    }
                    (
                        hax::CastKind::Pointer(hax::PointerCast::ReifyFnPointer),
                        src_ty @ Ty::Arrow(..),
                        tgt_ty @ Ty::Arrow(..),
                    ) => {
                        let src_ty = src_ty.clone();
                        let tgt_ty = tgt_ty.clone();
                        Ok(Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::FnPtr(src_ty, tgt_ty)),
                            op,
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
            hax::Rvalue::BinaryOp(binop, operands)
            | hax::Rvalue::CheckedBinaryOp(binop, operands) => {
                // We merge checked and unchecked binary operations
                let (left, right) = operands.deref();
                Ok(Rvalue::BinaryOp(
                    self.t_ctx.translate_binaryop_kind(span, *binop)?,
                    self.translate_operand(span, left)?,
                    self.translate_operand(span, right)?,
                ))
            }
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

                match aggregate_kind.deref() {
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

                        // Not sure what those two parameters are used for, so
                        // panicking if they are not none (to catch a use case).
                        // I'm not even sure that "field_index" is a proper name:
                        // the documentation seems outdated (it says the 4th parameter
                        // is a field index, while it makes more sense for it to be
                        // the 5th, and I don't know how I should use it anyway).
                        error_assert!(self, span, user_annotation.is_none());
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
                            AdtKind::Struct => Option::None,
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

                        let def_id = self.translate_fun_decl_id(span, DefId::from(def_id));
                        let akind = AggregateKind::Closure(def_id, generics);

                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    hax::AggregateKind::Generator(_def_id, _subst, _movability) => {
                        error_or_panic!(self, span, "Generators are not supported");
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
        args: Option<&Vec<hax::Operand>>,
        trait_refs: &Vec<hax::ImplExpr>,
        trait_info: &Option<hax::ImplExpr>,
    ) -> Result<SubstFunIdOrPanic, Error> {
        let rust_id = DefId::from(def_id);
        let name = self.t_ctx.hax_def_id_to_name(def_id)?;
        let is_local = rust_id.is_local();

        // Check if this function is a actually `panic`
        if name.equals_ref_name(&assumed::PANIC_NAME)
            || name.equals_ref_name(&assumed::BEGIN_PANIC_NAME)
            || name.equals_ref_name(&assumed::ASSERT_FAILED_NAME)
        {
            return Ok(SubstFunIdOrPanic::Panic);
        }

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
                    let arg = &args[0];
                    let t_arg = self.translate_move_box_first_projector_operand(span, arg)?;
                    Ok(vec![t_arg])
                })
                .transpose()?;

            // Return
            let func = FnPtr {
                func: FunIdOrTraitMethodRef::mk_assumed(AssumedFunId::BoxFree),
                generics: GenericArgs::new_from_types(vec![t_ty]),
            };
            let sfid = SubstFunId { func, args };
            Ok(SubstFunIdOrPanic::Fun(sfid))
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

            // Check if the function is considered primitive: primitive
            // functions benefit from special treatment.
            let is_prim = if is_local {
                false
            } else {
                assumed::get_fun_id_from_name(&name).is_some()
            };

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

            if !is_prim {
                // Two cases depending on whether we call a trait method or not
                match trait_info {
                    Option::None => {
                        // "Regular" function call
                        let def_id = self.translate_fun_decl_id(span, rust_id);
                        let func = FunIdOrTraitMethodRef::Fun(FunId::Regular(def_id));
                        let func = FnPtr { func, generics };
                        let sfid = SubstFunId { func, args };
                        Ok(SubstFunIdOrPanic::Fun(sfid))
                    }
                    Option::Some(trait_info) => {
                        // Trait method
                        let rust_id = DefId::from(def_id);
                        let impl_expr =
                            self.translate_trait_impl_expr(span, erase_regions, trait_info)?;
                        // The impl source should be Some(...): trait markers (that we may
                        // eliminate) don't have methods.
                        let impl_expr = impl_expr.unwrap();

                        trace!("{:?}", rust_id);

                        let trait_method_fun_id = self.translate_fun_decl_id(span, rust_id);
                        let method_name = self.t_ctx.translate_trait_item_name(rust_id)?;

                        let func = FunIdOrTraitMethodRef::Trait(
                            impl_expr,
                            method_name,
                            trait_method_fun_id,
                        );
                        let func = FnPtr { func, generics };
                        let sfid = SubstFunId { func, args };
                        Ok(SubstFunIdOrPanic::Fun(sfid))
                    }
                }
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
                assert!(trait_info.is_none());

                let aid = assumed::get_fun_id_from_name(&name).unwrap();

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

                let func = FnPtr {
                    func: FunIdOrTraitMethodRef::Fun(FunId::Assumed(aid)),
                    generics,
                };
                let sfid = SubstFunId { func, args };
                Ok(SubstFunIdOrPanic::Fun(sfid))
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
        let span = statement.source_info.span.rust_span_data.unwrap().span();

        use std::ops::Deref;

        use hax::StatementKind;
        let t_statement: Option<RawStatement> = match &*statement.kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = assign.deref();
                let t_place = self.translate_place(span, place)?;
                let t_rvalue = self.translate_rvalue(
                    statement.source_info.span.rust_span_data.unwrap().span(),
                    rvalue,
                )?;

                Some(RawStatement::Assign(t_place, t_rvalue))
            }
            StatementKind::FakeRead(info) => {
                let (_read_cause, place) = info.deref();
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

        // Add the meta information
        match t_statement {
            None => Ok(None),
            Some(t_statement) => {
                let meta = self
                    .t_ctx
                    .translate_meta_from_source_info(&body.source_scopes, &statement.source_info);

                Ok(Some(Statement::new(meta, t_statement)))
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
        let span = terminator.source_info.span.rust_span_data.unwrap().span();

        // Compute the meta information beforehand (we might need it to introduce
        // intermediate statements - we desugar some terminators)
        let meta = self
            .t_ctx
            .translate_meta_from_source_info(&body.source_scopes, &terminator.source_info);

        // Translate the terminator
        use hax::TerminatorKind;
        let t_terminator: RawTerminator = match &terminator.kind {
            TerminatorKind::Goto { target } => {
                let target = self.translate_basic_block_id(*target);
                RawTerminator::Goto { target }
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                // Translate the operand which gives the discriminant
                let (discr, discr_ty) = self.translate_operand_with_type(span, discr)?;

                // Translate the switch targets
                let targets = self.translate_switch_targets(&discr_ty, targets)?;

                RawTerminator::Switch { discr, targets }
            }
            TerminatorKind::Resume => {
                // This is used to correctly unwind. We shouldn't get there: if
                // we panic, the state gets stuck.
                error_or_panic!(self, span, "Unexpected terminator: resume");
            }
            TerminatorKind::Return => RawTerminator::Return,
            TerminatorKind::Unreachable => RawTerminator::Unreachable,
            TerminatorKind::Terminate => unimplemented!(),
            TerminatorKind::Drop {
                place,
                target,
                unwind: _, // We consider that panic is an error, and don't model unwinding
                replace: _,
            } => RawTerminator::Drop {
                place: self.translate_place(span, place)?,
                target: self.translate_basic_block_id(*target),
            },
            TerminatorKind::Call {
                fun,
                substs,
                args,
                destination,
                target,
                trait_refs,
                trait_info,
                unwind: _, // We consider that panic is an error, and don't model unwinding
                from_hir_call: _,
                fn_span: _,
            } => self.translate_function_call(
                span,
                fun,
                substs,
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
                let cond = self.translate_operand(span, cond)?;
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
                error_or_panic!(self, span, "Unsupported terminator: yield");
            }
            TerminatorKind::GeneratorDrop => {
                error_or_panic!(self, span, "Unsupported terminator: generator drop");
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
                error_or_panic!(self, span, "Inline assembly is not supported");
            }
        };

        // Add the meta information
        Ok(Terminator::new(meta, t_terminator))
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
                let targets_map: Vec<(ScalarValue, BlockId::Id)> = targets_map
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
        substs: &Vec<hax::GenericArg>,
        args: &Vec<hax::Operand>,
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
                    substs,
                    Some(args),
                    trait_refs,
                    trait_info,
                )?;

                match fid {
                    SubstFunIdOrPanic::Panic => {
                        // If the call is `panic!`, then the target is `None`.
                        // I don't know in which other cases it can be `None`.
                        assert!(target.is_none());

                        // We ignore the arguments
                        Ok(RawTerminator::Panic)
                    }
                    SubstFunIdOrPanic::Fun(fid) => {
                        let next_block = target.unwrap_or_else(|| {
                            panic!("Expected a next block after the call to {:?}.\n\nSubsts: {:?}\n\nArgs: {:?}:", rust_id, substs, args)
                        });

                        // Translate the target
                        let lval = self.translate_place(span, destination)?;
                        let next_block = self.translate_basic_block_id(next_block);

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

                // Translate the target
                let next_block = target.unwrap_or_else(|| {
                    panic!("Expected a next block after the call to {:?}.\n\nSubsts: {:?}\n\nArgs: {:?}:", p, substs, args)
                });
                let lval = self.translate_place(span, destination)?;
                let next_block = self.translate_basic_block_id(next_block);

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
        args: &Vec<hax::Operand>,
    ) -> Result<Vec<Operand>, Error> {
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
    ) -> Result<Option<ExprBody>, Error> {
        let tcx = self.t_ctx.tcx;

        if !self.t_ctx.id_is_transparent(rust_id)? {
            return Ok(None);
        }
        if !rust_id.is_local() && !self.t_ctx.extract_opaque_bodies {
            // We only extract non-local bodies if the `extract_opaque_bodies` option is set.
            return Ok(None);
        }

        // Retrive the body
        let Some(body) = get_mir_for_def_id_and_level(tcx, rust_id, self.t_ctx.mir_level)
        else { return Ok(None) };

        // Here, we have to create a MIR state, which contains the body
        let state = hax::state::State::new_from_mir(
            tcx,
            hax::options::Options {
                inline_macro_calls: Vec::new(),
            },
            // Yes, we have to clone, this is annoying: we end up cloning the body twice
            body.clone(),
            // Owner id
            rust_id,
        );
        // Translate
        let body: hax::MirBody<()> = body.sinto(&state);

        // Initialize the local variables
        trace!("Translating the body locals");
        self.translate_body_locals(&body)?;

        // Translate the expression body
        trace!("Translating the expression body");
        self.translate_transparent_expression_body(&body)?;

        // Compute the meta information
        let meta = self.translate_meta_from_rspan(body.span);

        // We need to convert the blocks map to an index vector
        // We clone things while we could move them...
        let mut blocks = BlockId::Vector::new();
        for (id, block) in self.blocks {
            let new_id = blocks.push(block);
            // Sanity check to make sure we don't mess with the indices
            assert!(id == new_id);
        }

        // Create the body
        Ok(Some(ExprBody {
            meta,
            arg_count,
            locals: self.vars,
            body: blocks,
        }))
    }

    /// Translate a function's signature, and initialize a body translation context
    /// at the same time - the function signature gives us the list of region and
    /// type parameters, that we put in the translation context.
    fn translate_function_signature(&mut self, def_id: DefId) -> Result<FunSig, Error> {
        let tcx = self.t_ctx.tcx;
        let erase_regions = false;
        let span = self.t_ctx.tcx.def_span(def_id);
        let is_closure = tcx.is_closure(def_id);
        let dep_src = DepSource::make(def_id, span);

        // The parameters (and in particular the lifetimes) are split between
        // early bound and late bound parameters. See those blog posts for explanations:
        // https://smallcultfollowing.com/babysteps/blog/2013/10/29/intermingled-parameter-lists/
        // https://smallcultfollowing.com/babysteps/blog/2013/11/04/intermingled-parameter-lists/
        // Note that only lifetimes can be late bound.
        //
        // [TyCtxt.generics_of] gives us the early-bound parameters
        // The late-bounds parameters are bound in the [Binder] returned by
        // [TyCtxt.type_of].

        // Retrieve the early bound parameters, and the late-bound parameters
        // through the function signature.
        let (substs, signature, closure_info): (
            Vec<hax::GenericArg>,
            rustc_middle::ty::Binder<'tcx, rustc_middle::ty::FnSig<'tcx>>,
            Option<(ClosureKind, Vec<rustc_middle::ty::Ty<'tcx>>)>,
        ) = if is_closure {
            // Closures have a peculiar handling in Rust: we can't call
            // `TyCtxt::fn_sig`.
            let fun_type = tcx.type_of(def_id).subst_identity();
            let rsubsts = match fun_type.kind() {
                ty::TyKind::Closure(_def_id, substs_ref) => substs_ref,
                _ => {
                    unreachable!()
                }
            };
            trace!("closure: rsubsts: {:?}", rsubsts);
            let closure = rsubsts.as_closure();
            // Retrieve the early bound parameters from the *parent* (i.e.,
            // the function in which the closure is actually defined).
            // Importantly, the type parameters necessarily come from the parents:
            // the closure can't itself be polymorphic, and the signature of
            // the closure only quantifies lifetimes.
            let substs = closure.parent_substs();
            trace!("closure.parent_substs: {:?}", substs);
            let sig = closure.sig();
            trace!("closure.sig: {:?}", sig);

            // Retrieve the kind of the closure
            let kind = match closure.kind() {
                rustc_middle::ty::ClosureKind::Fn => ClosureKind::Fn,
                rustc_middle::ty::ClosureKind::FnMut => ClosureKind::FnMut,
                rustc_middle::ty::ClosureKind::FnOnce => ClosureKind::FnOnce,
            };

            // Retrieve the type of the captured stated
            let state: Vec<rustc_middle::ty::Ty<'tcx>> = closure.upvar_tys().collect();

            let substs = substs.sinto(&self.hax_state);

            trace!("closure.sig_as_fn_ptr_ty: {:?}", closure.sig_as_fn_ptr_ty());
            trace!("closure.kind_ty: {:?}", closure.kind_ty());
            trace!(
                "closure.print_as_impl_trait: {:?}",
                closure.print_as_impl_trait()
            );

            // Sanity check: the parent subst only contains types and generics
            error_assert!(
                self,
                span,
                substs
                    .iter()
                    .all(|bv| !matches!(bv, hax::GenericArg::Lifetime(_))),
                "The closure parent parameters contain regions"
            );

            (substs, sig, Some((kind, state)))
        } else {
            // Retrieve the signature
            let fn_sig = tcx.fn_sig(def_id);
            trace!("Fun sig: {:?}", fn_sig);
            // There is an early binder for the early-bound regions, that
            // we ignore, and a binder for the late-bound regions, that we
            // keep.
            let fn_sig = fn_sig.subst_identity();

            // Retrieve the early-bound parameters
            let fun_type = tcx.type_of(def_id).subst_identity();
            let substs: Vec<hax::GenericArg> = match fun_type.kind() {
                ty::TyKind::FnDef(_def_id, substs_ref) => substs_ref.sinto(&self.hax_state),
                ty::TyKind::Closure(_, _) => {
                    unreachable!()
                }
                _ => {
                    unreachable!()
                }
            };

            (substs, fn_sig, None)
        };
        let signature: hax::MirPolyFnSig = signature.sinto(&self.hax_state);

        // Start by translating the early-bound parameters (those are contained by `substs`).
        // Some debugging information:
        trace!("Def id: {def_id:?}:\n\n- substs:\n{substs:?}\n\n- generics:\n{:?}\n\n- signature bound vars:\n{:?}\n\n- signature:\n{:?}\n",
               tcx.generics_of(def_id), signature.bound_vars, signature);

        // Add the *early-bound* parameters.
        self.translate_generic_params_from_hax(span, &substs)?;

        //
        // Add the *late-bound* parameters (bound in the signature, can only be lifetimes)
        //
        let is_unsafe = match signature.value.unsafety {
            hax::Unsafety::Unsafe => true,
            hax::Unsafety::Normal => false,
        };
        let bvar_names = signature
            .bound_vars
            .into_iter()
            .map(|bvar| {
                // There should only be regions in the late-bound parameters
                use hax::BoundVariableKind;
                match bvar {
                    BoundVariableKind::Region(br) => Ok(translate_bound_region_kind_name(&br)),
                    BoundVariableKind::Ty(_) | BoundVariableKind::Const => {
                        error_or_panic!(
                            self,
                            span,
                            format!("Unexpected bound variable: {:?}", bvar)
                        )
                    }
                }
            })
            .try_collect()?;
        let signature = signature.value;

        self.set_first_bound_regions_group(bvar_names);
        let fun_kind = &self.t_ctx.get_item_kind(&dep_src, def_id)?;

        // Add the trait clauses
        self.while_registering_trait_clauses(move |ctx| {
            // Add the ctx trait clause if it is a trait decl item
            match fun_kind {
                ItemKind::Regular => (),
                ItemKind::TraitItemImpl { impl_id, .. } => {
                    ctx.add_trait_impl_self_trait_clause(*impl_id)?;
                }
                ItemKind::TraitItemProvided(..) | ItemKind::TraitItemDecl(..) => {
                    // This is a trait decl item
                    let trait_id = tcx.trait_of_item(def_id).unwrap();
                    ctx.add_self_trait_clause(trait_id)?;
                }
            }

            // Translate the predicates (in particular, the trait clauses)
            match &fun_kind {
                ItemKind::Regular | ItemKind::TraitItemImpl { .. } => {
                    ctx.translate_predicates_of(None, def_id)?;
                }
                ItemKind::TraitItemProvided(trait_decl_id, ..)
                | ItemKind::TraitItemDecl(trait_decl_id, ..) => {
                    ctx.translate_predicates_of(Some(*trait_decl_id), def_id)?;
                }
            }

            // Solve the unsolved obligations
            ctx.solve_trait_obligations_in_trait_clauses(span);
            Ok(())
        })?;

        // Translate the signature
        trace!("signature of {def_id:?}:\n{:?}", signature);
        let inputs: Vec<Ty> = signature
            .inputs
            .iter()
            .map(|ty| self.translate_ty(span, erase_regions, ty))
            .try_collect()?;
        let output = self.translate_ty(span, erase_regions, &signature.output)?;

        let fmt_ctx = self.into_fmt();
        trace!(
            "# Input variables types:\n{}",
            iterator_to_string(&|x| fmt_ctx.format_object(x), inputs.iter())
        );
        trace!(
            "# Output variable type:\n{}",
            fmt_ctx.format_object(&output)
        );

        // Compute the additional information for closures
        let closure_info = if let Some((kind, state_tys)) = closure_info {
            let erase_regions = false;
            let state = state_tys
                .into_iter()
                .map(|ty| self.translate_ty(span, erase_regions, &ty.sinto(&self.hax_state)))
                .try_collect::<Vec<Ty>>()?;

            Some(ClosureInfo { kind, state })
        } else {
            None
        };

        let mut parent_params_info = self.get_function_parent_params_info(&dep_src, def_id)?;
        // If this is a trait decl method, we need to adjust the number of parent clauses
        if matches!(
            fun_kind,
            ItemKind::TraitItemProvided(..) | ItemKind::TraitItemDecl(..)
        ) {
            if let Some(info) = &mut parent_params_info {
                // All the trait clauses are registered as parent (of Self)
                // trait clauses, not as local trait clauses.
                info.num_trait_clauses = 0;
            }
        }

        Ok(FunSig {
            generics: self.get_generics(),
            preds: self.get_predicates(),
            is_unsafe,
            is_closure,
            closure_info,
            parent_params_info,
            inputs,
            output,
        })
    }

    fn get_function_parent_params_info(
        &mut self,
        src: &Option<DepSource>,
        def_id: DefId,
    ) -> Result<Option<ParamsInfo>, Error> {
        let kind = self.t_ctx.get_item_kind(src, def_id)?;
        let info = match kind {
            ItemKind::Regular => None,
            ItemKind::TraitItemImpl { .. }
            | ItemKind::TraitItemDecl { .. }
            | ItemKind::TraitItemProvided { .. } => {
                Some(self.get_parent_params_info(def_id)?.unwrap())
            }
        };
        Ok(info)
    }
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// Translate one function.
    pub(crate) fn translate_function(&mut self, rust_id: DefId) {
        self.with_def_id(rust_id, |ctx| {
            if ctx.translate_function_aux(rust_id).is_err() {
                let span = ctx.tcx.def_span(rust_id);
                ctx.span_err(
                    span,
                    &format!(
                        "Ignoring the following function due to an error: {:?}",
                        rust_id
                    ),
                );
                // Save the definition
                let _ = ctx.ignored_failed_decls.insert(rust_id);
            }
        });
    }

    /// Auxliary helper to properly handle errors, see [translate_function].
    pub fn translate_function_aux(&mut self, rust_id: DefId) -> Result<(), Error> {
        trace!("About to translate function:\n{:?}", rust_id);
        let def_id = self.translate_fun_decl_id(&None, rust_id);
        let def_span = self.tcx.def_span(rust_id);

        // Compute the meta information
        let meta = self.translate_meta_from_rid(rust_id);

        // Initialize the body translation context
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        // Translate the function name
        let name = bt_ctx.t_ctx.def_id_to_name(rust_id)?;

        // Check whether this function is a method declaration for a trait definition.
        // If this is the case, it shouldn't contain a body.
        let kind = bt_ctx
            .t_ctx
            .get_item_kind(&DepSource::make(rust_id, def_span), rust_id)?;
        let is_trait_method_decl = match &kind {
            ItemKind::Regular
            | ItemKind::TraitItemImpl { .. }
            | ItemKind::TraitItemProvided(..) => false,
            ItemKind::TraitItemDecl(..) => true,
        };

        // Translate the function signature
        trace!("Translating function signature");
        let signature = bt_ctx.translate_function_signature(rust_id)?;

        let body = if !is_trait_method_decl {
            // Translate the body. This returns `None` if we can't/decide not to translate this
            // body.
            match bt_ctx.translate_body(rust_id, signature.inputs.len()) {
                Ok(body) => body,
                // Error case: we could have a variant for this
                Err(_) => None,
            }
        } else {
            None
        };

        // Save the new function
        self.fun_decls.insert(
            def_id,
            FunDecl {
                meta,
                def_id,
                rust_id,
                is_local: rust_id.is_local(),
                name,
                signature,
                kind,
                body,
            },
        );

        Ok(())
    }

    /// Translate one global.
    pub(crate) fn translate_global(&mut self, rust_id: DefId) {
        self.with_def_id(rust_id, |ctx| {
            if ctx.translate_global_aux(rust_id).is_err() {
                let span = ctx.tcx.def_span(rust_id);
                ctx.span_err(
                    span,
                    &format!(
                        "Ignoring the following global due to an error: {:?}",
                        rust_id
                    ),
                );
                // Save the definition
                let _ = ctx.ignored_failed_decls.insert(rust_id);
            }
        });
    }

    /// Auxliary helper to properly handle errors, see [translate_global].
    pub fn translate_global_aux(&mut self, rust_id: DefId) -> Result<(), Error> {
        trace!("About to translate global:\n{:?}", rust_id);
        let span = self.tcx.def_span(rust_id);

        let def_id = self.translate_global_decl_id(&None, rust_id);

        // Compute the meta information
        let meta = self.translate_meta_from_rid(rust_id);

        // Initialize the body translation context
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        // Check and translate the generics - globals *can* have generics
        // Ex.:
        // ```
        // impl<const N : usize> Foo<N> {
        //   const LEN : usize = N;
        // }
        // ```
        bt_ctx.translate_generic_params(rust_id)?;
        bt_ctx.translate_predicates_solve_trait_obligations_of(None, rust_id)?;

        let hax_state = &bt_ctx.hax_state;

        // Translate the global name
        let name = bt_ctx.t_ctx.def_id_to_name(rust_id)?;

        trace!("Translating global type");
        let mir_ty = bt_ctx.t_ctx.tcx.type_of(rust_id).subst_identity();
        let erase_regions = false; // This doesn't matter: there shouldn't be any regions
        let ty = bt_ctx.translate_ty(span, erase_regions, &mir_ty.sinto(hax_state))?;

        // Retrieve the kind
        let kind = bt_ctx
            .t_ctx
            .get_item_kind(&DepSource::make(rust_id, span), rust_id)?;

        let generics = bt_ctx.get_generics();
        let preds = bt_ctx.get_predicates();

        // Translate its body like the body of a function. This returns `None` if we can't/decide
        // not to translate this body.
        let body = match bt_ctx.translate_body(rust_id, 0) {
            Ok(body) => body,
            // Error case: we could have a specific variant
            Err(_) => None,
        };

        // Save the new global
        self.global_decls.insert(
            def_id,
            GlobalDecl {
                def_id,
                rust_id,
                meta,
                is_local: rust_id.is_local(),
                name,
                generics,
                preds,
                ty,
                kind,
                body,
            },
        );

        Ok(())
    }
}
