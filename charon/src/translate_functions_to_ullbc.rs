//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

#![allow(dead_code)]
use crate::assumed;
use crate::common::*;
use crate::expressions::*;
use crate::formatter::Formatter;
use crate::get_mir::{boxes_are_desugared, get_mir_for_def_id_and_level};
use crate::id_vector;
use crate::names_utils::{def_id_to_name, extended_def_id_to_name};
use crate::regions_hierarchy::RegionGroups;
use crate::translate_ctx::*;
use crate::translate_types;
use crate::types::*;
use crate::ullbc_ast::*;
use crate::values::*;
use core::convert::*;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir::START_BLOCK;
use rustc_middle::ty;
use std::iter::FromIterator;
use translate_types::{translate_bound_region_kind_name, translate_region_name};

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

fn translate_binaryop_kind(binop: hax::BinOp) -> BinOp {
    match binop {
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
        hax::BinOp::Shl => BinOp::Shl,
        hax::BinOp::Shr => BinOp::Shr,
        _ => {
            unreachable!();
        }
    }
}

fn translate_unaryop_kind(binop: hax::UnOp) -> UnOp {
    match binop {
        hax::UnOp::Not => UnOp::Not,
        hax::UnOp::Neg => UnOp::Neg,
    }
}

/// Build an uninterpreted constant from a MIR constant identifier.
fn rid_as_unevaluated_constant<'tcx>(id: DefId) -> rustc_middle::mir::UnevaluatedConst<'tcx> {
    let p = ty::List::empty();
    rustc_middle::mir::UnevaluatedConst::new(id, p)
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
    pub(crate) fn get_fun_kind(&mut self, rust_id: DefId) -> FunKind {
        trace!("rust_id: {:?}", rust_id);
        let tcx = self.tcx;
        if let Some(assoc) = tcx.opt_associated_item(rust_id) {
            match assoc.container {
                ty::AssocItemContainer::ImplContainer => {
                    // This method is defined in an impl block.
                    // It can be a regular function in an impl block or a trait
                    // method implementation.
                    //
                    // Ex.:
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

                    // Check if there is a trait item (if yes, it is a trait method
                    // implementation, if no it is a regular function).
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
                        None => FunKind::Regular,
                        Some(trait_method_id) => {
                            let trait_id = tcx.trait_of_item(trait_method_id).unwrap();
                            let trait_id = self.translate_trait_decl_id(trait_id);
                            // The trait id should be Some(...): trait markers (that we
                            // may eliminate) don't have methods.
                            let trait_id = trait_id.unwrap();

                            // Retrieve the id of the impl block
                            let impl_id = self
                                .translate_trait_impl_id(tcx.predicates_of(rust_id).parent.unwrap())
                                .unwrap();

                            let method_name = self.translate_trait_item_name(trait_method_id);

                            // Check if the current function implements a provided method.
                            // We do so by retrieving the def id of the method which is
                            // implemented, and checking its kind.
                            let provided = match self.get_fun_kind(trait_method_id) {
                                FunKind::TraitMethodDecl(..) => false,
                                FunKind::TraitMethodProvided(..) => true,
                                FunKind::Regular | FunKind::TraitMethodImpl { .. } => {
                                    unreachable!()
                                }
                            };

                            FunKind::TraitMethodImpl {
                                impl_id,
                                trait_id,
                                method_name,
                                provided,
                            }
                        }
                    }
                }
                ty::AssocItemContainer::TraitContainer => {
                    // This method is the *declaration* of a trait method
                    // Ex.:
                    // ====
                    // ```
                    // trait Foo {
                    //   fn baz(...); // <- declaration of a trait method
                    // }
                    // ```

                    // Yet, this could be a default method implementation, in which
                    // case there is a body: we need to check that.

                    // In order to check if this is a provided method, we check
                    // the defaultness (i.e., whether the method has a default value):
                    let is_provided = tcx.impl_defaultness(rust_id).has_value();

                    // Compute additional information
                    let method_name = self.translate_trait_item_name(rust_id);
                    let trait_id = tcx.trait_of_item(rust_id).unwrap();
                    let trait_id = self.translate_trait_decl_id(trait_id);
                    // The trait id should be Some(...): trait markers (that we
                    // may eliminate) don't have methods.
                    let trait_id = trait_id.unwrap();

                    if is_provided {
                        FunKind::TraitMethodProvided(trait_id, method_name)
                    } else {
                        FunKind::TraitMethodDecl(trait_id, method_name)
                    }
                }
            }
        } else {
            FunKind::Regular
        }
    }
}

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    /// Translate a function's local variables by adding them in the environment.
    fn translate_body_locals(&mut self, body: &hax::MirBody<()>) -> Result<()> {
        // Translate the parameters
        for (index, var) in body.local_decls.raw.iter().enumerate() {
            trace!("Translating local of index {} and type {:?}", index, var.ty);

            // Find the name of the variable
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
        assert!(id == START_BLOCK_ID);

        Ok(())
    }

    fn translate_basic_block(
        &mut self,
        body: &hax::MirBody<()>,
        block_id: hax::BasicBlock,
    ) -> Result<BlockId::Id> {
        // Check if the block has already been translated
        if let Some(id) = self.blocks_map.get(&block_id) {
            return Ok(id);
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
        let terminator = block.terminator.as_ref().unwrap();
        let terminator = self.translate_terminator(body, terminator)?;

        // Insert the block in the translated blocks
        let block = BlockData {
            statements,
            terminator,
        };

        self.push_block(nid, block);

        Ok(nid)
    }

    /// Translate a place and return its type
    fn translate_place_with_type(&mut self, place: &hax::Place) -> (Place, ETy) {
        let ty = self.translate_ety(&place.ty).unwrap();
        let (var_id, projection) = self.translate_projection(place);
        (Place { var_id, projection }, ty)
    }

    /// Translate a place
    fn translate_place(&mut self, place: &hax::Place) -> Place {
        self.translate_place_with_type(place).0
    }

    /// Translate a place - TODO: rename
    /// TODO: Hax represents places in a different manner than MIR. We should
    /// update our representation of places to match the Hax representation.
    /// TODO: we don't need to return the projected type, it is directly
    /// given by the place.
    fn translate_projection(&mut self, place: &hax::Place) -> (VarId::Id, Projection) {
        match &place.kind {
            hax::PlaceKind::Local(local) => {
                let var_id = self.get_local(&local).unwrap();
                (var_id, Vec::new())
            }
            hax::PlaceKind::Projection { place, kind } => {
                let (var_id, mut projection) = self.translate_projection(&*place);
                // Compute the type of the value *before* projection - we use this
                // to disambiguate
                let current_ty = self.translate_ety(&place.ty).unwrap();
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
                                let variant_id = variant.map(|vid| translate_variant_id(vid));
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
                                    Ty::Adt(TypeId::Assumed(AssumedTy::Option), generics) => {
                                        assert!(generics.regions.is_empty());
                                        assert!(generics.types.len() == 1);
                                        assert!(generics.const_generics.is_empty());
                                        assert!(field_id == FieldId::ZERO);

                                        let variant_id = variant_id.unwrap();
                                        assert!(variant_id == assumed::OPTION_SOME_VARIANT_ID);
                                        let proj_kind = FieldProjKind::Option(variant_id);
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
                                        unreachable!();
                                    }
                                }
                            }
                        };
                        projection.push(proj_elem);
                    }
                    hax::ProjectionElem::Index(local) => {
                        let local = self.get_local(&local).unwrap();
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
                        unimplemented!()
                    }
                    hax::ProjectionElem::OpaqueCast => {
                        // Don't know what that is
                        unimplemented!()
                    }
                };

                // Return
                (var_id, projection)
            }
        }
    }

    /// Translate an operand with its type
    fn translate_operand_with_type(&mut self, operand: &hax::Operand) -> (Operand, ETy) {
        trace!();
        match operand {
            hax::Operand::Copy(place) => {
                let (p, ty) = self.translate_place_with_type(place);
                (Operand::Copy(p), ty)
            }
            hax::Operand::Move(place) => {
                let (p, ty) = self.translate_place_with_type(place);
                (Operand::Move(p), ty)
            }
            hax::Operand::Constant(constant) => {
                let constant = self.translate_constant_to_constant_expr(constant);
                let ty = constant.ty.clone();
                (Operand::Const(constant), ty)
            }
        }
    }

    /// Translate an operand
    fn translate_operand(&mut self, operand: &hax::Operand) -> Operand {
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
    fn translate_move_box_first_projector_operand(&mut self, operand: &hax::Operand) -> Operand {
        trace!();
        match operand {
            hax::Operand::Move(place) => {
                let place = self.translate_place(place);

                // Sanity check
                let var = self.get_var_from_id(place.var_id).unwrap();
                assert!(var.ty.is_box());

                Operand::Move(place)
            }
            _ => {
                unreachable!();
            }
        }
    }

    /// Translate an rvalue
    fn translate_rvalue(&mut self, rvalue: &hax::Rvalue) -> Rvalue {
        use std::ops::Deref;
        match rvalue {
            hax::Rvalue::Use(operand) => Rvalue::Use(self.translate_operand(operand)),
            hax::Rvalue::CopyForDeref(place) => {
                // According to the documentation, it seems to be an optimisation
                // for drop elaboration. We treat it as a regular copy.
                let place = self.translate_place(place);
                Rvalue::Use(Operand::Copy(place))
            }
            hax::Rvalue::Repeat(operand, cnst) => {
                let c = self.translate_constant_expr_to_const_generic(cnst);
                let (operand, t) = self.translate_operand_with_type(operand);
                // Remark: we could desugar this into a function call later.
                Rvalue::Repeat(operand, t, c)
            }
            hax::Rvalue::Ref(_region, borrow_kind, place) => {
                let place = self.translate_place(place);
                let borrow_kind = translate_borrow_kind(*borrow_kind);
                Rvalue::Ref(place, borrow_kind)
            }
            hax::Rvalue::ThreadLocalRef(_) => {
                unreachable!();
            }
            hax::Rvalue::AddressOf(_, _) => {
                unreachable!();
            }
            hax::Rvalue::Len(place) => {
                let (place, ty) = self.translate_place_with_type(place);
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
                Rvalue::Len(place, ty, cg)
            }
            hax::Rvalue::Cast(cast_kind, operand, tgt_ty) => {
                trace!("Rvalue::Cast: {:?}", rvalue);
                // Put aside the pointer casts (which we don't support), I think
                // casts should only be from integers/booleans to integer/booleans.

                // Translate the target type
                let tgt_ty = self.translate_ety(tgt_ty).unwrap();

                // Translate the operand
                let (op, src_ty) = self.translate_operand_with_type(operand);

                match (cast_kind, &src_ty, &tgt_ty) {
                    (hax::CastKind::IntToInt, _, _) => {
                        // We only support source and target types for integers
                        let tgt_ty = *tgt_ty.as_literal().as_integer();
                        let src_ty = *src_ty.as_literal().as_integer();

                        Rvalue::UnaryOp(UnOp::Cast(CastKind::Integer(src_ty, tgt_ty)), op)
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
                                Rvalue::UnaryOp(
                                    UnOp::ArrayToSlice(
                                        *kind1,
                                        generics.types[0].clone(),
                                        generics.const_generics[0].clone(),
                                    ),
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
                    (
                        hax::CastKind::Pointer(hax::PointerCast::ClosureFnPointer(unsafety)),
                        Ty::Arrow(inputs1, output1),
                        Ty::Arrow(inputs2, output2),
                    ) => {
                        assert!(*unsafety == hax::Unsafety::Normal);
                        let src_ty = Ty::Arrow(inputs1.clone(), output1.clone()).to_rty();
                        let tgt_ty = Ty::Arrow(inputs2.clone(), output2.clone()).to_rty();
                        Rvalue::UnaryOp(UnOp::Cast(CastKind::FnPtr(src_ty, tgt_ty)), op)
                    }
                    _ => {
                        panic!(
                            "Unsupported cast:\n- rvalue: {:?}\n- src={:?}\n- dst={:?}",
                            rvalue, src_ty, tgt_ty
                        )
                    }
                }
            }
            hax::Rvalue::BinaryOp(binop, operands)
            | hax::Rvalue::CheckedBinaryOp(binop, operands) => {
                // We merge checked and unchecked binary operations
                let (left, right) = operands.deref();
                Rvalue::BinaryOp(
                    translate_binaryop_kind(*binop),
                    self.translate_operand(left),
                    self.translate_operand(right),
                )
            }
            hax::Rvalue::NullaryOp(nullop, _ty) => {
                trace!("NullOp: {:?}", nullop);
                // Nullary operations are very low-level and shouldn't be necessary
                // unless one needs to write unsafe code.
                unreachable!();
            }
            hax::Rvalue::UnaryOp(unop, operand) => Rvalue::UnaryOp(
                translate_unaryop_kind(*unop),
                self.translate_operand(operand),
            ),
            hax::Rvalue::Discriminant(place) => Rvalue::Discriminant(self.translate_place(place)),
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
                    .map(|op| self.translate_operand(op))
                    .collect();

                match aggregate_kind.deref() {
                    hax::AggregateKind::Array(ty) => {
                        let t_ty = self.translate_ety(ty).unwrap();
                        let cg = ConstGeneric::Value(Literal::Scalar(ScalarValue::Usize(
                            operands_t.len() as u64,
                        )));
                        Rvalue::Aggregate(AggregateKind::Array(t_ty, cg), operands_t)
                    }
                    hax::AggregateKind::Tuple => {
                        Rvalue::Aggregate(AggregateKind::Tuple, operands_t)
                    }
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
                        assert!(user_annotation.is_none());
                        assert!(field_index.is_none());

                        // Translate the substitution
                        let mut generics = self
                            .translate_substs_and_trait_refs_in_body(None, substs, trait_refs)
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

                            let akind = AggregateKind::Adt(id_t, variant_id, generics);

                            Rvalue::Aggregate(akind, operands_t)
                        } else {
                            // External ADT.
                            // Can be `Option`
                            // TODO: treat all external ADTs in a consistant manner.
                            // For instance, we can access the variants of any external
                            // enumeration marked as `public`.
                            let name = def_id_to_name(self.t_ctx.tcx, adt_id);
                            if name.equals_ref_name(&assumed::OPTION_NAME) {
                                // Sanity checks
                                assert!(generics.regions.is_empty());
                                assert!(generics.types.len() == 1);

                                // Find the variant
                                let variant_id = translate_variant_id(*variant_idx);
                                if variant_id == assumed::OPTION_NONE_VARIANT_ID {
                                    assert!(operands_t.is_empty());
                                } else if variant_id == assumed::OPTION_SOME_VARIANT_ID {
                                    assert!(operands_t.len() == 1);
                                } else {
                                    unreachable!();
                                }

                                let akind = AggregateKind::Option(
                                    variant_id,
                                    generics.types.pop().unwrap(),
                                );

                                Rvalue::Aggregate(akind, operands_t)
                            } else if name.equals_ref_name(&assumed::RANGE_NAME) {
                                // Sanity checks
                                assert!(generics.regions.is_empty());
                                // Ranges are parametric over the type of indices
                                assert!(generics.types.len() == 1);
                                Rvalue::Aggregate(
                                    AggregateKind::Range(generics.types.pop().unwrap()),
                                    operands_t,
                                )
                            } else {
                                panic!("Unsupported ADT: {}", name);
                            }
                        }
                    }
                    hax::AggregateKind::Closure(def_id, sig) => {
                        trace!("Closure:\n- def_id: {:?}\n- sig: {:?}", def_id, sig);
                        // We need to register the signature for def_id, so that
                        // we can later translate the closure the same way as top-level
                        // functions.
                        todo!();
                        /*let def_id = self.translate_fun_decl_id(def_id.rust_def_id.unwrap());
                        let akind = AggregateKind::Closure(def_id);
                        Rvalue::Aggregate(akind, Vec::new()) */
                    }
                    hax::AggregateKind::Generator(_def_id, _subst, _movability) => {
                        unimplemented!();
                    }
                }
            }
            hax::Rvalue::ShallowInitBox(_, _) => {
                unimplemented!();
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
    pub(crate) fn translate_fun_decl_id_with_args(
        &mut self,
        def_id: &hax::DefId,
        substs: &Vec<hax::GenericArg>,
        args: Option<&Vec<hax::Operand>>,
        trait_refs: &Vec<hax::ImplSource>,
        trait_info: &Option<hax::TraitInfo>,
    ) -> SubstFunIdOrPanic {
        let rust_id = def_id.rust_def_id.unwrap();
        let name = def_id_to_name(self.t_ctx.tcx, def_id);
        let is_local = rust_id.is_local();

        // Check if this function is a actually `panic`
        if name.equals_ref_name(&assumed::PANIC_NAME)
            || name.equals_ref_name(&assumed::BEGIN_PANIC_NAME)
        {
            return SubstFunIdOrPanic::Panic;
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
                self.translate_ety(ty).unwrap()
            } else {
                unreachable!()
            };

            let args = args.map(|args| {
                assert!(args.len() == 2);
                // Translate the first argument - note that we use a special
                // function to translate it: the operand should be of the form:
                // `move b.0`, and if it is the case it will return `move b`
                let arg = &args[0];
                let t_arg = self.translate_move_box_first_projector_operand(arg);
                vec![t_arg]
            });

            // Return
            let func = FnPtr {
                func: FunIdOrTraitMethodRef::mk_assumed(AssumedFunId::BoxFree),
                generics: GenericArgs::new_from_types(vec![t_ty]),
                trait_and_method_generic_args: None,
            };
            let sfid = SubstFunId { func, args };
            SubstFunIdOrPanic::Fun(sfid)
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
            let generics = self
                .translate_substs_and_trait_refs_in_body(used_type_args, substs, trait_refs)
                .unwrap();

            // Translate the arguments
            let args = args.map(|args| self.translate_arguments(used_args, args));

            // Check if the function is considered primitive: primitive
            // functions benefit from special treatment.
            let is_prim = if is_local {
                false
            } else {
                assumed::get_fun_id_from_name(&name, &generics.types).is_some()
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
                // Two cases depending on whether we call a trait function
                // or not.
                match trait_info {
                    Option::None => {
                        let def_id = self.translate_fun_decl_id(rust_id);
                        let func = FunIdOrTraitMethodRef::Fun(FunId::Regular(def_id));
                        let func = FnPtr {
                            func,
                            generics,
                            trait_and_method_generic_args: None,
                        };
                        let sfid = SubstFunId { func, args };
                        SubstFunIdOrPanic::Fun(sfid)
                    }
                    Option::Some(trait_info) => {
                        let rust_id = def_id.rust_def_id.unwrap();
                        let impl_source = self
                            .translate_trait_impl_source_erased_regions(&trait_info.impl_source);
                        // The impl source should be Some(...): trait markers (that we may
                        // eliminate) don't have methods.
                        let impl_source = impl_source.unwrap();

                        trace!("{:?}", rust_id);

                        let trait_method_fun_id = self.translate_fun_decl_id(rust_id);
                        let method_name = self.t_ctx.translate_trait_item_name(rust_id);

                        // Compute the concatenation of all the generic arguments which were given to
                        // the function (trait arguments + method arguments).
                        let trait_and_method_generic_args = {
                            let (regions, types, const_generics) = self
                                .translate_substs(None, &trait_info.all_generics)
                                .unwrap();

                            // When concatenating the trait refs we have to be careful:
                            // - if we refer to an implementation, we must concatenate the
                            //   trait references given to the impl source
                            // - if we refer to a clause, we must retrieve the
                            //   parent trait clauses.
                            let trait_refs = match &impl_source.trait_id {
                                TraitInstanceId::TraitImpl(_) => impl_source
                                    .generics
                                    .trait_refs
                                    .iter()
                                    .chain(generics.trait_refs.iter())
                                    .cloned()
                                    .collect(),
                                _ => impl_source
                                    .trait_decl_ref
                                    .generics
                                    .trait_refs
                                    .iter()
                                    .chain(generics.trait_refs.iter())
                                    .cloned()
                                    .collect(),
                            };
                            Some(GenericArgs {
                                regions,
                                types,
                                const_generics,
                                trait_refs,
                            })
                        };

                        let func = FunIdOrTraitMethodRef::Trait(
                            impl_source,
                            method_name,
                            trait_method_fun_id,
                        );
                        let func = FnPtr {
                            func,
                            generics,
                            trait_and_method_generic_args,
                        };
                        let sfid = SubstFunId { func, args };
                        SubstFunIdOrPanic::Fun(sfid)
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

                // TODO: remove the cases for vector index, box deref, etc.
                // assert!(trait_info.is_none());

                let aid = assumed::get_fun_id_from_name(&name, &generics.types).unwrap();
                let mut generics = generics;

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
                    AssumedFunId::Replace
                    | AssumedFunId::BoxNew
                    | AssumedFunId::VecNew
                    | AssumedFunId::VecPush
                    | AssumedFunId::VecInsert
                    | AssumedFunId::VecLen
                    | AssumedFunId::SliceLen => {
                        // Nothing to do
                    }
                    AssumedFunId::BoxDeref | AssumedFunId::BoxDerefMut => {
                        // Translate `std::Deref::deref` or `std::DerefMut::deref_mut` applied
                        // on boxes. We need a custom function because it is a trait.
                        // TODO: treat in a general manner

                        // Check the arguments
                        assert!(generics.regions.is_empty());
                        assert!(generics.types.len() == 1);

                        // For now we only support deref on boxes
                        // Retrieve the boxed value
                        let arg_ty = generics.types.get(0).unwrap(); // should be `Box<...>`
                        let boxed_ty = arg_ty.as_box();
                        if boxed_ty.is_none() {
                            panic!(
                                "Deref/DerefMut trait applied with parameter {:?} while it is only supported on Box<T> values",
                                arg_ty
                            );
                        }
                        let boxed_ty = boxed_ty.unwrap();
                        generics.types = vec![boxed_ty.clone()];
                    }
                    AssumedFunId::VecIndex | AssumedFunId::VecIndexMut => {
                        // This is actually a trait
                        // TODO: treat it in a general manner

                        // Check the arguments
                        assert!(generics.regions.is_empty());
                        assert!(generics.types.len() == 1);

                        // For now we only support index on vectors
                        // Retrieve the boxed value
                        let arg_ty = generics.types.get(0).unwrap(); // should be `Vec<...>`
                        let arg_ty = match arg_ty.as_vec() {
                            Option::Some(ty) => ty,
                            Option::None => {
                                panic!(
                                    "Index/IndexMut trait applied with parameter {:?} while it is only supported on Vec<T> values",
                                    arg_ty
                                );
                            }
                        };
                        generics.types = vec![arg_ty.clone()];
                    }
                    AssumedFunId::ArraySubsliceShared
                    | AssumedFunId::ArraySubsliceMut
                    | AssumedFunId::SliceSubsliceShared
                    | AssumedFunId::SliceSubsliceMut => {
                        // Take a subslice from an array/slice.
                        // Note that this isn't any different from a regular function call. Ideally,
                        // we'd have a generic assumed function mechanism.
                        assert!(generics.types.len() == 1);
                        assert!(generics.const_generics.is_empty());
                        // We need to unwrap the type to retrieve the `T` inside the `Slice<T>`
                        // or the `Array<T, N>`
                        let (_, generics) = generics.types[0].clone().to_adt();
                        assert!(generics.types.len() == 1);
                        assert!(generics.const_generics.len() <= 1);
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
                    trait_and_method_generic_args: None,
                };
                let sfid = SubstFunId { func, args };
                SubstFunIdOrPanic::Fun(sfid)
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
    ) -> Result<Option<Statement>> {
        trace!("About to translate statement (MIR) {:?}", statement);

        use std::ops::Deref;

        use hax::StatementKind;
        let t_statement: Option<RawStatement> = match &*statement.kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = assign.deref();
                let t_place = self.translate_place(place);
                let t_rvalue = self.translate_rvalue(rvalue);

                Some(RawStatement::Assign(t_place, t_rvalue))
            }
            StatementKind::FakeRead(info) => {
                let (_read_cause, place) = info.deref();
                let t_place = self.translate_place(place);

                Some(RawStatement::FakeRead(t_place))
            }
            StatementKind::PlaceMention(place) => {
                // Simply accesses a place. Introduced for instance in place
                // of `let _ = ...`. We desugar it to a fake read.
                let t_place = self.translate_place(place);

                Some(RawStatement::FakeRead(t_place))
            }
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                let t_place = self.translate_place(place);
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
                unimplemented!();
            }
            StatementKind::Nop => {
                // We ignore this statement
                None
            }
            StatementKind::Deinit(place) => {
                let t_place = self.translate_place(place);
                Some(RawStatement::Deinit(t_place))
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
    ) -> Result<Terminator> {
        trace!("About to translate terminator (MIR) {:?}", terminator);

        // Compute the meta information beforehand (we might need it to introduce
        // intermediate statements - we desugar some terminators)
        let meta = self
            .t_ctx
            .translate_meta_from_source_info(&body.source_scopes, &terminator.source_info);

        // Translate the terminator
        use hax::TerminatorKind;
        let t_terminator: RawTerminator = match &terminator.kind {
            TerminatorKind::Goto { target } => {
                let target = self.translate_basic_block(body, *target)?;
                RawTerminator::Goto { target }
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                // Translate the operand which gives the discriminant
                let (discr, discr_ty) = self.translate_operand_with_type(discr);

                // Translate the switch targets
                let targets = self.translate_switch_targets(body, &discr_ty, targets);

                RawTerminator::Switch { discr, targets }
            }
            TerminatorKind::Resume => {
                // This is used to correctly unwind. We shouldn't get there: if
                // we panic, the state gets stuck.
                unreachable!();
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
                place: self.translate_place(place),
                target: self.translate_basic_block(body, *target)?,
            },
            TerminatorKind::Call {
                fun_id,
                substs,
                args,
                destination,
                target,
                trait_refs,
                trait_info,
                unwind: _, // We consider that panic is an error, and don't model unwinding
                from_hir_call: _,
                fn_span: _,
            } => {
                trace!("Call: func: {:?}", fun_id.rust_def_id);
                self.translate_function_call(
                    body,
                    fun_id,
                    substs,
                    args,
                    destination,
                    target,
                    trait_refs,
                    trait_info,
                )?
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
                RawTerminator::Goto { target }
            }
            TerminatorKind::FalseUnwind {
                real_target,
                unwind: _,
            } => {
                // We consider this to be a goto
                let target = self.translate_basic_block(body, *real_target)?;
                RawTerminator::Goto { target }
            }
            TerminatorKind::InlineAsm { .. } => {
                // This case should have been eliminated during the registration phase
                unreachable!();
            }
        };

        // Add the meta information
        Ok(Terminator::new(meta, t_terminator))
    }

    /// Translate switch targets
    fn translate_switch_targets(
        &mut self,
        body: &hax::MirBody<()>,
        switch_ty: &ETy,
        targets: &hax::SwitchTargets,
    ) -> SwitchTargets {
        trace!("targets: {:?}", targets);
        match targets {
            hax::SwitchTargets::If(if_block, then_block) => {
                let if_block = self.translate_basic_block(body, *if_block).unwrap();
                let then_block = self.translate_basic_block(body, *then_block).unwrap();
                SwitchTargets::If(if_block, then_block)
            }
            hax::SwitchTargets::SwitchInt(_, targets_map, otherwise) => {
                let int_ty = *switch_ty.as_literal().as_integer();
                let targets_map = targets_map
                    .iter()
                    .map(|(v, tgt)| {
                        let v = ScalarValue::from_le_bytes(int_ty, v.data_le_bytes);
                        let tgt = self.translate_basic_block(body, *tgt).unwrap();
                        (v, tgt)
                    })
                    .collect();
                let otherwise = self.translate_basic_block(body, *otherwise).unwrap();
                SwitchTargets::SwitchInt(int_ty, targets_map, otherwise)
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
        trait_refs: &Vec<hax::ImplSource>,
        trait_info: &Option<hax::TraitInfo>,
    ) -> Result<RawTerminator> {
        trace!();
        let rust_id = def_id.rust_def_id.unwrap();

        // Translate the function operand - should be a constant: we don't
        // support closures for now
        trace!("func: {:?}", rust_id);

        // Translate the function id, with its parameters
        let fid = self.translate_fun_decl_id_with_args(
            def_id,
            substs,
            Some(args),
            trait_refs,
            trait_info,
        );

        match fid {
            SubstFunIdOrPanic::Panic => {
                // If the call is `panic!`, then the target is `None`.
                // I don't know in which other cases it can be `None`.
                assert!(target.is_none());

                // We ignore the arguments
                Ok(RawTerminator::Panic)
            }
            SubstFunIdOrPanic::Fun(fid) => {
                let next_block = target.unwrap();

                // Translate the target
                let lval = self.translate_place(destination);
                let next_block = self.translate_basic_block(body, next_block)?;

                let call = Call {
                    func: fid.func,
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

    pub(crate) fn translate_substs_and_trait_refs_in_body(
        &mut self,
        used_args: Option<Vec<bool>>,
        substs: &Vec<hax::GenericArg>,
        trait_refs: &Vec<hax::ImplSource>,
    ) -> Result<EGenericArgs> {
        trace!("{:?}", substs);
        let (regions, types, const_generics) = self.translate_substs(used_args, substs)?;
        let trait_refs = self.translate_trait_impl_sources_erased_regions(trait_refs);
        Ok(GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        })
    }

    /// Evaluate function arguments in a context, and return the list of computed
    /// values.
    fn translate_arguments(
        &mut self,
        used_args: Option<Vec<bool>>,
        args: &Vec<hax::Operand>,
    ) -> Vec<Operand> {
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

    fn translate_body(mut self, local_id: LocalDefId, arg_count: usize) -> Result<ExprBody> {
        let tcx = self.t_ctx.tcx;

        // Retrive the body
        let body = get_mir_for_def_id_and_level(tcx, local_id, self.t_ctx.mir_level);

        // Here, we have to create a MIR state, which contains the body
        let state = hax::state::State::new_from_mir(
            tcx,
            hax::options::Options {
                inline_macro_calls: Vec::new(),
            },
            // Yes, we have to clone, this is annoying: we end up cloning the body twice
            body.clone(),
            // Owner id
            local_id.to_def_id(),
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
            use crate::id_vector::ToUsize;
            // Sanity check to make sure we don't mess with the indices
            assert!(id.to_usize() == blocks.len());
            blocks.push_back(block);
        }

        // Create the body
        Ok(ExprBody {
            meta,
            arg_count,
            locals: self.vars,
            body: blocks,
        })
    }

    /// Translate a function's signature, and initialize a body translation context
    /// at the same time - the function signature gives us the list of region and
    /// type parameters, that we put in the translation context.
    fn translate_function_signature(&mut self, def_id: DefId) -> FunSig {
        let tcx = self.t_ctx.tcx;

        // Retrieve the function signature, which includes the lifetimes
        let signature: rustc_middle::ty::Binder<'tcx, rustc_middle::ty::FnSig<'tcx>> =
            if tcx.is_closure(def_id) {
                // TODO:
                // ```
                // error: internal compiler error: compiler/rustc_hir_analysis/src/collect.rs:1118:13:
                // to get the signature of a closure, use `substs.as_closure().sig()` not `fn_sig()`
                // ```
                //
                // We need to have a map from def ids to signatures, for the
                // closures. We also need to replace the vectors of type variables,
                // regions, etc. with maps, because the indices will not always
                // start at 0.
                todo!("{:?}", tcx.type_of(def_id))
            } else {
                tcx.fn_sig(def_id).subst_identity()
            };

        // The parameters (and in particular the lifetimegs) are split between
        // early bound and late bound parameters. See those blog posts for explanations:
        // https://smallcultfollowing.com/babysteps/blog/2013/10/29/intermingled-parameter-lists/
        // https://smallcultfollowing.com/babysteps/blog/2013/11/04/intermingled-parameter-lists/
        // Note that only lifetimes can be late bound.
        //
        // [TyCtxt.generics_of] gives us the early-bound parameters
        // The late-bounds parameters are bound in the [Binder] returned by
        // [TyCtxt.type_of].

        // Start by translating the early-bound parameters (those are contained by `substs`).
        let fun_type = tcx.type_of(def_id).subst_identity();
        let substs = match fun_type.kind() {
            ty::TyKind::FnDef(_def_id, substs_ref) => substs_ref,
            _ => {
                unreachable!()
            }
        };
        let substs = substs.sinto(&self.hax_state);

        // Some debugging information:
        trace!("Def id: {def_id:?}:\n\n- generics:\n{:?}\n\n- substs:\n{:?}\n\n- signature bound vars:\n{:?}\n\n- signature:\n{:?}\n",
               tcx.generics_of(def_id), substs, signature.bound_vars(), signature);

        // Add the early-bound parameters.
        // TODO: use the generics instead of the substs ([TyCtxt.generics_of])? In
        // practice is easier to use the subst. For instance, in the subst, the
        // constant generics are typed.
        for param in substs {
            use hax::GenericArg;
            match param {
                GenericArg::Type(param_ty) => {
                    // This type should be a param type
                    match param_ty {
                        hax::Ty::Param(param_ty) => {
                            self.push_type_var(param_ty.index, param_ty.name);
                        }
                        _ => {
                            unreachable!();
                        }
                    }
                }
                GenericArg::Lifetime(region) => {
                    let name = translate_region_name(&region);
                    self.push_region(region, name);
                }
                GenericArg::Const(c) => {
                    let ty = self.translate_ety(&c.ty).unwrap();
                    let ty = ty.to_literal();
                    match *c.contents {
                        hax::ConstantExprKind::ConstRef { id: cp } => {
                            self.push_const_generic_var(cp.index, ty, cp.name);
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }

        // Add the late bound parameters (bound in the signature, can only be lifetimes)
        let signature: hax::MirPolyFnSig = signature.sinto(&self.hax_state);

        let bvar_names = signature
            .bound_vars
            .into_iter()
            .map(|bvar| {
                // There should only be regions in the late-bound parameters
                use hax::BoundVariableKind;
                match bvar {
                    BoundVariableKind::Region(br) => translate_bound_region_kind_name(&br),
                    BoundVariableKind::Ty(_) | BoundVariableKind::Const => {
                        unreachable!()
                    }
                }
            })
            .collect();
        self.push_bound_regions_group(bvar_names);

        // Add the self trait clause if it is a trait decl item - we take care
        // of adding it before translating the predicates.
        match self.t_ctx.get_fun_kind(def_id) {
            FunKind::Regular => (),
            FunKind::TraitMethodImpl { .. } => (),
            FunKind::TraitMethodProvided(..) | FunKind::TraitMethodDecl(..) => {
                // This is a trait decl item
                let trait_id = tcx.trait_of_item(def_id).unwrap();
                self.add_self_trait_clause(trait_id);
            }
        }

        // Translate the predicates (in particular, the trait clauses)
        self.translate_predicates_of(def_id);

        // Translate the signature
        let signature = signature.value;
        trace!("signature of {def_id:?}:\n{:?}", signature);
        let inputs: Vec<RTy> = Vec::from_iter(
            signature
                .inputs
                .iter()
                .map(|ty| self.translate_sig_ty(ty).unwrap()),
        );
        let output = self.translate_sig_ty(&signature.output).unwrap();

        trace!(
            "# Input variables types:\n{}",
            iterator_to_string(&|x| self.format_object(x), inputs.iter())
        );
        trace!("# Output variable type:\n{}", self.format_object(&output));

        let parent_params_info = self.get_function_parent_params_info(def_id);

        FunSig {
            generics: self.get_generics(),
            preds: self.get_predicates(),
            regions_hierarchy: RegionGroups::new(), // Hierarchy not yet computed
            parent_params_info,
            inputs,
            output,
        }
    }

    fn get_function_parent_params_info(&mut self, def_id: DefId) -> Option<ParamsInfo> {
        let kind = self.t_ctx.get_fun_kind(def_id);
        match kind {
            FunKind::Regular => None,
            FunKind::TraitMethodImpl { .. }
            | FunKind::TraitMethodDecl { .. }
            | FunKind::TraitMethodProvided { .. } => {
                Some(self.get_parent_params_info(def_id).unwrap())
            }
        }
    }
}

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    /// Translate one function.
    pub(crate) fn translate_function(&mut self, rust_id: DefId) {
        trace!("About to translate function:\n{:?}", rust_id);
        let def_id = self.translate_fun_decl_id(rust_id);
        let is_transparent = self.id_is_transparent(rust_id);

        // Compute the meta information
        let meta = self.translate_meta_from_rid(rust_id);

        // Initialize the body translation context
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);

        // Translate the function name
        let name = extended_def_id_to_name(&rust_id.sinto(&bt_ctx.hax_state));

        // Check whether this function is a method declaration for a trait definition.
        // If this is the case, it shouldn't contain a body.
        let kind = bt_ctx.t_ctx.get_fun_kind(rust_id);
        let is_trait_method_decl = match &kind {
            FunKind::Regular
            | FunKind::TraitMethodImpl { .. }
            | FunKind::TraitMethodProvided(..) => false,
            FunKind::TraitMethodDecl(..) => true,
        };

        // Translate the function signature
        trace!("Translating function signature");
        let signature = bt_ctx.translate_function_signature(rust_id);

        // Check if the type is opaque or transparent
        let is_local = rust_id.is_local();

        let body = if !is_transparent || !is_local || is_trait_method_decl {
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
            FunDecl {
                meta,
                def_id,
                name,
                signature,
                kind,
                body,
            },
        );
    }

    /// Generate an expression body from a typed constant value.
    fn global_generate_assignment_body(
        &mut self,
        ty: ETy,
        def_rid: DefId,
        val: ConstantExpr,
    ) -> ExprBody {
        // Compute the meta information (we use the same everywhere)
        let meta = self.translate_meta_from_rid(def_rid);

        // # Variables
        // ret : ty
        let var = Var {
            index: VarId::ZERO,
            name: None,
            ty,
        };
        // # Instructions
        // ret := const (ty, val)
        // return
        let block = BlockData {
            statements: vec![Statement::new(
                meta,
                RawStatement::Assign(Place::new(var.index), Rvalue::Use(Operand::Const(val))),
            )],
            terminator: Terminator::new(meta, RawTerminator::Return),
        };
        ExprBody {
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

        // Compute the meta information
        let meta = self.translate_meta_from_rid(rust_id);
        let is_transparent = self.id_is_transparent(rust_id);

        // Initialize the body translation context
        let mut bt_ctx = BodyTransCtx::new(rust_id, self);
        let hax_state = &bt_ctx.hax_state;

        // Translate the global name
        let name = extended_def_id_to_name(&rust_id.sinto(hax_state));

        trace!("Translating global type");
        let mir_ty = bt_ctx.t_ctx.tcx.type_of(rust_id).subst_identity();
        let ty = bt_ctx.translate_ety(&mir_ty.sinto(hax_state)).unwrap();

        let body = if rust_id.is_local() && is_transparent {
            // It's a local and transparent global: we extract its body as for functions.
            Some(bt_ctx.translate_body(rust_id.expect_local(), 0).unwrap())
        } else {
            // Otherwise do nothing
            None
        };

        // Save the new global
        self.global_defs.insert(
            def_id,
            GlobalDecl {
                def_id,
                meta,
                name,
                ty,
                body,
            },
        );
    }
}
