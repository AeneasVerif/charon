//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

use itertools::Itertools;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::mem;
use std::ops::Deref;
use std::ops::DerefMut;
use std::panic;
use std::rc::Rc;

use crate::hax;
use rustc_middle::mir;
use rustc_middle::ty;
use rustc_span::{Symbol, sym};

use super::translate_crate::*;
use super::translate_ctx::*;
use charon_lib::formatter::{FmtCtx, IntoFormatter, compute_local_names};
use charon_lib::name_matcher::NamePattern;
use charon_lib::pretty::FmtWithCtx;
use charon_lib::ullbc_ast::*;

/// A translation context for function bodies.
pub(crate) struct BodyTransCtx<'tcx, 'tctx, 'ictx> {
    /// The translation context for the item.
    pub i_ctx: &'ictx mut ItemTransCtx<'tcx, 'tctx>,
    /// List of body locals.
    pub local_decls: &'ictx rustc_index::IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
    /// Types supplied explicitly by the user.
    pub user_type_annotations: ty::CanonicalUserTypeAnnotations<'tcx>,

    /// What kind of drops we get in this body.
    pub drop_kind: DropKind,
    /// The (regular) variables in the current function body.
    pub locals: Locals,
    /// The map from rust variable indices to translated variables indices.
    pub locals_map: HashMap<usize, LocalId>,
    /// The translated blocks.
    pub blocks: IndexMap<BlockId, BlockData>,
    /// The map from rust blocks to translated blocks.
    /// Note that when translating terminators like DropAndReplace, we might have
    /// to introduce new blocks which don't appear in the original MIR.
    pub blocks_map: HashMap<mir::BasicBlock, BlockId>,
    /// We register the blocks to translate in a stack, so as to avoid
    /// writing the translation functions as recursive functions. We do
    /// so because we had stack overflows in the past.
    pub blocks_stack: VecDeque<mir::BasicBlock>,
}

impl<'tcx, 'tctx, 'ictx> BodyTransCtx<'tcx, 'tctx, 'ictx> {
    pub(crate) fn new(
        i_ctx: &'ictx mut ItemTransCtx<'tcx, 'tctx>,
        body: &'ictx Rc<mir::Body<'tcx>>,
        drop_kind: DropKind,
    ) -> Self {
        i_ctx.lifetime_freshener = Some(IndexMap::new());
        let mut user_type_annotations = body.user_type_annotations.clone();
        if let RustcItem::Mono(item) = &i_ctx.item_src.item {
            // `CanonicalUserTypeAnnotation::user_ty` is deliberately not folded when rustc
            // instantiates a MIR body, so do the item substitution explicitly.
            let item = item.clone();
            let args = item.rustc_args(i_ctx.hax_state_with_id());
            for annotation in &mut user_type_annotations {
                annotation.user_ty.value = hax::substitute(
                    i_ctx.tcx,
                    hax::UnderOwnerState::typing_env(&i_ctx.hax_state),
                    Some(args),
                    annotation.user_ty.value,
                );
            }
        }
        BodyTransCtx {
            i_ctx,
            local_decls: &body.local_decls,
            user_type_annotations,
            drop_kind,
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

/// A translation context for function blocks.
pub(crate) struct BlockTransCtx<'tcx, 'tctx, 'ictx, 'bctx> {
    /// The translation context for the item.
    pub b_ctx: &'bctx mut BodyTransCtx<'tcx, 'tctx, 'ictx>,
    /// Block onto which we're adding statements.
    pub current_block: BlockId,
    /// List of currently translated statements
    pub statements: Vec<Statement>,
}

impl<'tcx, 'tctx, 'ictx, 'bctx> BlockTransCtx<'tcx, 'tctx, 'ictx, 'bctx> {
    pub(crate) fn new(
        b_ctx: &'bctx mut BodyTransCtx<'tcx, 'tctx, 'ictx>,
        current_block: BlockId,
    ) -> Self {
        BlockTransCtx {
            b_ctx,
            current_block,
            statements: Vec::new(),
        }
    }

    fn finish_current_block(self, terminator: Terminator) {
        let block = BlockData {
            statements: self.statements,
            terminator,
        };
        self.b_ctx.blocks.set_slot(self.current_block, block);
    }

    /// Used for non-diverging intrinsics.
    fn push_nounwind_call(&mut self, span: Span, call: Call) {
        let target = self.blocks.reserve_slot();
        let on_unwind = self.blocks.push(
            Terminator::new(span, TerminatorKind::Abort(AbortKind::UndefinedBehavior)).into_block(),
        );
        let block = BlockData {
            statements: mem::take(&mut self.statements),
            terminator: Terminator::new(
                span,
                TerminatorKind::Call {
                    call,
                    target,
                    on_unwind,
                },
            ),
        };
        let current_block = mem::replace(&mut self.current_block, target);
        self.blocks.set_slot(current_block, block);
    }
}

impl<'tcx, 'tctx, 'ictx, 'bctx> Deref for BlockTransCtx<'tcx, 'tctx, 'ictx, 'bctx> {
    type Target = BodyTransCtx<'tcx, 'tctx, 'ictx>;
    fn deref(&self) -> &Self::Target {
        self.b_ctx
    }
}
impl<'tcx, 'tctx, 'ictx, 'bctx> DerefMut for BlockTransCtx<'tcx, 'tctx, 'ictx, 'bctx> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.b_ctx
    }
}

impl<'tcx> TranslateCtx<'tcx> {
    pub fn translate_variant_id(&self, id: hax::VariantIdx) -> VariantId {
        VariantId::new(id.as_usize())
    }

    pub fn translate_field_id(&self, id: hax::FieldIdx) -> FieldId {
        FieldId::new(id.index())
    }

    fn translate_borrow_kind(&self, borrow_kind: mir::BorrowKind) -> BorrowKind {
        match borrow_kind {
            mir::BorrowKind::Shared => BorrowKind::Shared,
            mir::BorrowKind::Mut { kind } => match kind {
                mir::MutBorrowKind::Default => BorrowKind::Mut,
                mir::MutBorrowKind::TwoPhaseBorrow => BorrowKind::TwoPhaseMut,
                mir::MutBorrowKind::ClosureCapture => BorrowKind::UniqueImmutable,
            },
            mir::BorrowKind::Fake(mir::FakeBorrowKind::Shallow) => BorrowKind::Shallow,
            // This one is used only in deref patterns.
            mir::BorrowKind::Fake(mir::FakeBorrowKind::Deep) => unimplemented!(),
        }
    }
}

impl<'tcx> ItemTransCtx<'tcx, '_> {
    /// Translate the MIR body of this definition if it has one. Catches any error and returns
    /// `Body::Error` instead
    pub fn translate_def_body(&mut self, span: Span, def: &hax::FullDef<'tcx>) -> Body {
        match self.translate_def_body_inner(span, def) {
            Ok(body) => body,
            Err(e) => Body::Error(e),
        }
    }

    fn translate_def_body_inner(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
    ) -> Result<Body, Error> {
        // Retrieve the body
        if let Some(body) = self.get_mir(def.this(), span)? {
            Ok(self.translate_body(span, body, &def.source_text))
        } else if let Some(value) = self.evaluate_const_def(def) {
            // For globals without MIR, generate a body by evaluating the global. This is how we
            // get the value of statics (which have no cross-crate MIR at all) and of "trivial"
            // consts (whose value rustc stores directly instead of encoding MIR for it).
            let c = self.translate_constant_expr(span, &value)?;
            let mut bb = BodyBuilder::new(span, 0);
            let ret = bb.new_var(None, c.ty().clone());
            bb.push_statement(StatementKind::Assign(
                ret,
                Rvalue::Use(Operand::Const(c), WithRetag::No),
            ));
            Ok(Body::Unstructured(bb.build()))
        } else {
            Ok(Body::Missing)
        }
    }

    /// Translate a function body. Catches errors and returns `Body::Error` instead.
    /// That's the entrypoint of this module.
    pub fn translate_body(
        &mut self,
        span: Span,
        body: mir::Body<'tcx>,
        source_text: &Option<String>,
    ) -> Body {
        let _guard = charon_lib::timing::scope("translate-body");
        let drop_kind = match body.phase {
            mir::MirPhase::Built | mir::MirPhase::Analysis(..) => DropKind::Conditional,
            mir::MirPhase::Runtime(..) => DropKind::Precise,
        };
        let mut ctx = panic::AssertUnwindSafe(&mut *self);
        let body = panic::AssertUnwindSafe(body);
        // Stopgap measure because there are still many panics in charon and hax.
        let res = panic::catch_unwind(move || {
            let body = Rc::new({ body }.0);
            let ctx = BodyTransCtx::new(*ctx, &body, drop_kind);
            ctx.translate_body(&body, source_text)
        });
        match res {
            Ok(Ok(body)) => body,
            // Translation error
            Ok(Err(e)) => Body::Error(e),
            // Panic
            Err(_) => {
                let e = register_error!(self, span, "Thread panicked when extracting body.");
                Body::Error(e)
            }
        }
    }

    fn translate_unsizing_metadata(
        &mut self,
        span: Span,
        meta: hax::UnsizingMetadata,
    ) -> Result<UnsizingMetadata, Error> {
        Ok(match &meta {
            hax::UnsizingMetadata::Length(len) => {
                let len = self.translate_constant_expr(span, len)?;
                UnsizingMetadata::Length(len)
            }
            hax::UnsizingMetadata::DirectVTable(trait_proof) => {
                let tref = self.translate_trait_proof(span, trait_proof)?;
                let vtable = self.translate_vtable_instance_const(span, trait_proof)?;
                UnsizingMetadata::VTable(tref, vtable)
            }
            hax::UnsizingMetadata::NestedVTable(dyn_trait_proof) => {
                // This binds a fake `T: SrcTrait` variable.
                let binder =
                    self.translate_dyn_binder(span, dyn_trait_proof, |ctx, _, trait_proof| {
                        ctx.translate_trait_proof(span, trait_proof)
                    })?;

                // Compute the supertrait path from the source tref to the target
                // tref.
                let mut target_tref = &binder.skip_binder;
                let mut clause_path: Vec<(TraitDeclId, TraitClauseId)> = vec![];
                while let TraitRefKind::ParentClause(tref, id) = &target_tref.kind {
                    clause_path.push((tref.trait_decl_ref.skip_binder.id, *id));
                    target_tref = tref;
                }

                let mut field_path = vec![];
                for &(trait_id, clause_id) in &clause_path {
                    if let Ok(ItemRef::TraitDecl(tdecl)) = self.get_or_translate(trait_id.into())
                        && let vtable_decl_id = tdecl.vtable.as_ref().unwrap().id
                        && let Ok(ItemRef::Type(vtable_decl)) =
                            self.get_or_translate(vtable_decl_id.into())
                    {
                        let TypeSource::VTable { supertrait_map, .. } = &vtable_decl.src else {
                            unreachable!()
                        };
                        field_path.push(supertrait_map[clause_id].unwrap());
                    } else {
                        break;
                    }
                }

                if field_path.len() == clause_path.len() {
                    UnsizingMetadata::VTableUpcast(field_path)
                } else {
                    UnsizingMetadata::Unknown
                }
            }
            hax::UnsizingMetadata::Unknown => UnsizingMetadata::Unknown,
        })
    }

    /// Generate a fake function body for ADT constructors.
    pub(crate) fn build_ctor_body(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
    ) -> Result<Body, Error> {
        let hax::FullDefKind::Ctor {
            adt_def_id,
            ctor_of,
            variant_id,
            fields,
            output_ty,
            ..
        } = def.kind()
        else {
            unreachable!()
        };
        let tref = self
            .translate_type_decl_ref(span, &def.this().with_def_id(self.hax_state(), adt_def_id))?;
        let output_ty = self.translate_ty(span, output_ty)?;

        let mut builder = BodyBuilder::new(span, fields.len());
        let return_place = builder.new_var(None, output_ty);
        let args: Vec<_> = fields
            .iter()
            .map(|field| -> Result<Operand, Error> {
                let ty = self.translate_ty(span, &field.ty)?;
                let place = builder.new_var(None, ty);
                Ok(Operand::Move(place))
            })
            .try_collect()?;
        let variant = match ctor_of {
            hax::CtorOf::Struct => None,
            hax::CtorOf::Variant => Some(self.translate_variant_id(*variant_id)),
        };
        builder.push_statement(StatementKind::Assign(
            return_place,
            Rvalue::Aggregate(AggregateKind::Adt(tref, variant, None), args),
        ));
        Ok(Body::Unstructured(builder.build()))
    }

    /// FIXME(#865): Generate a function body for the `box_assume_init_into_vec_unsafe` function,
    /// because the MIR we get for it is too optimized to be usable.
    pub(crate) fn build_box_assume_init_into_vec_unsafe(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
    ) -> Result<Body, Error> {
        // pub fn box_assume_init_into_vec_unsafe<T, const N: usize>(
        //     b: Box<MaybeUninit<[T; N]>>,
        // ) -> Vec<T> {
        //     let x: Box<[T; N]> = unsafe { Box::assume_init(b) };
        //     let y = x as Box<[T]>;
        //     core::slice::into_vec(y)
        // }
        let tcx = self.tcx;
        let hax::FullDefKind::Fn { sig: hax_sig, .. } = def.kind() else {
            unreachable!()
        };
        let hax_sig = hax_sig.hax_skip_binder_ref();
        let sig = self.translate_fun_sig(span, hax_sig)?;

        // Get the `[T; N]` and `A` parameters.
        let (array_rust_ty, alloc_rust_ty) = {
            let input_box_rust_args = {
                let hax::TyKind::Adt(input_box_item) = hax_sig.inputs[0].kind() else {
                    raise_error!(self, span, "expected a boxed input in the hax signature");
                };
                input_box_item.rustc_args(self.hax_state_with_id())
            };
            let maybe_uninit_array_rust_ty = input_box_rust_args[0].as_type().unwrap();
            let alloc_rust_ty = input_box_rust_args[1].as_type().unwrap();
            let ty::Adt(_, maybe_uninit_rust_args) = maybe_uninit_array_rust_ty.kind() else {
                raise_error!(
                    self,
                    span,
                    "expected `MaybeUninit<[T; N]>` in the hax signature"
                );
            };
            let Some(array_rust_ty) = maybe_uninit_rust_args[0].as_type() else {
                raise_error!(
                    self,
                    span,
                    "expected the first `MaybeUninit` parameter to be a type"
                );
            };
            (array_rust_ty, alloc_rust_ty)
        };
        // `T`
        let elem_rust_ty = array_rust_ty.builtin_index().unwrap();
        // `[T]`
        let slice_rust_ty = ty::Ty::new_slice(tcx, elem_rust_ty);
        // `Box<[T; N]>`
        let box_array_rust_ty = ty::Ty::new_box(tcx, array_rust_ty);
        let box_array_ty = self.translate_rustc_ty(span, &box_array_rust_ty)?;
        // `Box<[T]>`
        let box_slice_rust_ty = ty::Ty::new_box(tcx, slice_rust_ty);
        let box_slice_ty = self.translate_rustc_ty(span, &box_slice_rust_ty)?;

        if !self.monomorphize() {
            // Make `Box::new` and `Box::write` available to a later construction pass.
            let path = NamePattern::parse(names::BOX_NEW).unwrap();
            let box_new_def_id = self
                .resolve_path(span, &path, true)?
                .into_iter()
                .exactly_one()
                .unwrap();
            let box_new_args = tcx.mk_args(&[array_rust_ty.into()]);
            let box_new_item =
                hax::ItemRef::translate(self.hax_state_with_id(), box_new_def_id, box_new_args);
            let _ = self.translate_fn_ptr(span, &box_new_item, TransItemSourceKind::Fun)?;

            let path = NamePattern::parse(names::BOX_WRITE).unwrap();
            let box_write_def_id = self
                .resolve_path(span, &path, true)?
                .into_iter()
                .exactly_one()
                .unwrap();
            let box_write_args = tcx.mk_args(&[array_rust_ty.into(), alloc_rust_ty.into()]);
            let box_write_item =
                hax::ItemRef::translate(self.hax_state_with_id(), box_write_def_id, box_write_args);
            let _ = self.translate_fn_ptr(span, &box_write_item, TransItemSourceKind::Fun)?;
        }

        let body = {
            let mut builder = BodyBuilder::new(span, sig.inputs.len());
            let return_place = builder.new_var(Some("ret".to_string()), sig.output.clone());
            let input = builder.new_var(Some("b".to_string()), sig.inputs[0].clone());
            let initialized_box = builder.new_var(Some("x".to_string()), box_array_ty.clone());
            let box_slice = builder.new_var(Some("y".to_string()), box_slice_ty.clone());

            builder.call({
                let assume_init_fn = {
                    let path = NamePattern::parse("alloc::boxed::Box::assume_init").unwrap();
                    let assume_init_def_id = self
                        .resolve_path(span, &path, true)?
                        .into_iter()
                        // There's `assume_init` on `Box<MU<T>>` and `Box<[MU<T>]>`, we want the former.
                        .filter(|&def_id| {
                            let sig = self.tcx.fn_sig(def_id);
                            !sig.skip_binder().inputs().skip_binder()[0]
                                .expect_boxed_ty()
                                .is_slice()
                        })
                        .exactly_one()
                        .unwrap();
                    let assume_init_args =
                        tcx.mk_args(&[array_rust_ty.into(), alloc_rust_ty.into()]);
                    let assume_init_item = hax::ItemRef::translate(
                        self.hax_state_with_id(),
                        assume_init_def_id,
                        assume_init_args,
                    );
                    self.translate_fn_ptr(span, &assume_init_item, TransItemSourceKind::Fun)?
                };
                Call {
                    func: FnOperand::Regular(assume_init_fn),
                    args: vec![Operand::Move(input)],
                    dest: initialized_box.clone(),
                }
            });

            builder.push_statement({
                let meta = hax::compute_unsizing_metadata(
                    &self.hax_state,
                    box_array_rust_ty,
                    box_slice_rust_ty,
                );
                let meta = self.translate_unsizing_metadata(span, meta)?;
                StatementKind::Assign(
                    box_slice.clone(),
                    Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::Unsize(box_array_ty, box_slice_ty, meta)),
                        Operand::Move(initialized_box),
                    ),
                )
            });

            builder.call({
                let into_vec_fn = {
                    let path = NamePattern::parse("slice::into_vec").unwrap();
                    let into_vec_def_id = self
                        .resolve_path(span, &path, true)?
                        .into_iter()
                        .exactly_one()
                        .unwrap();
                    let into_vec_args = tcx.mk_args(&[elem_rust_ty.into(), alloc_rust_ty.into()]);
                    let into_vec_item = hax::ItemRef::translate(
                        self.hax_state_with_id(),
                        into_vec_def_id,
                        into_vec_args,
                    );
                    self.translate_fn_ptr(span, &into_vec_item, TransItemSourceKind::Fun)?
                };
                Call {
                    func: FnOperand::Regular(into_vec_fn),
                    args: vec![Operand::Move(box_slice)],
                    dest: return_place,
                }
            });
            builder.build()
        };

        Ok(Body::Unstructured(body))
    }

    /// Generate a function body for `core::intrinsics::type_id`.
    pub(crate) fn build_type_id_body(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
        signature: &FunSig,
    ) -> Result<Body, Error> {
        let generics = self.translate_generic_args(span, &def.this().generic_args, &[])?;
        let type_id_ty = generics.types[0].clone();

        let mut builder = BodyBuilder::new(span, signature.inputs.len());
        let return_place = builder.new_var(Some("ret".to_string()), signature.output.clone());
        let type_id = ConstantExpr::new(
            ConstantExprKind::TypeId(type_id_ty),
            signature.output.clone(),
        );
        builder.push_statement(StatementKind::Assign(
            return_place,
            Rvalue::Use(Operand::Const(type_id), WithRetag::No),
        ));
        Ok(Body::Unstructured(builder.build()))
    }

    /// Generate a function body for `core::ptr::drop_glue`.
    pub(crate) fn build_drop_glue_body(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
        signature: &FunSig,
    ) -> Result<Body, Error> {
        let hax::FullDefKind::Fn { .. } = def.kind() else {
            unreachable!()
        };
        let def_id = def.def_id().as_real_def_id().unwrap();
        let rustc_args = def.this().rustc_args(self.hax_state_with_id());
        let rustc_sig = self.tcx.fn_sig(def_id).instantiate(self.tcx, rustc_args);
        // `skip_binder` is ok because we have that lifetime in scope.
        let input_ty = rustc_sig.skip_binder().inputs()[0];
        let pointee_ty = input_ty
            .builtin_deref(true)
            .expect("`drop_glue` argument is not a pointer");
        let fn_ptr = self.translate_drop_glue_method_call(span, pointee_ty)?;

        let mut builder = BodyBuilder::new(span, signature.inputs.len());
        let _return_place = builder.new_var(Some("ret".to_string()), signature.output.clone());
        let input = builder.new_var(None, signature.inputs[0].clone());
        builder.insert_drop(input.deref(), fn_ptr);
        Ok(Body::Unstructured(builder.build()))
    }
}

impl<'tcx> BodyTransCtx<'tcx, '_, '_> {
    pub(crate) fn translate_local(&self, local: &mir::Local) -> Option<LocalId> {
        self.locals_map.get(&local.index()).copied()
    }

    pub(crate) fn push_var(&mut self, rid: mir::Local, ty: Ty, name: Option<String>, span: Span) {
        let local_id = self.locals.locals.push_with(|index| Local {
            index,
            name,
            span,
            ty,
        });
        self.locals_map.insert(rid.as_usize(), local_id);
    }

    /// Translate a function's local variables by adding them in the environment.
    fn translate_body_locals(&mut self, body: &mir::Body<'tcx>) -> Result<(), Error> {
        // Translate the parameters
        for (index, var) in body.local_decls.iter_enumerated() {
            // Find the name of the variable
            let name: Option<String> = hax::name_of_local(index, &body.var_debug_info);

            // Translate the type
            let span = self.translate_span(&var.source_info.span);
            let ty = self.translate_rustc_ty(span, &var.ty)?;

            // Add the variable to the environment
            self.push_var(index, ty, name, span);
        }

        Ok(())
    }

    /// Translate a basic block id and register it, if it hasn't been done.
    fn translate_basic_block_id(&mut self, block_id: mir::BasicBlock) -> BlockId {
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
        block_id: BlockId,
        source_scopes: &rustc_index::IndexVec<mir::SourceScope, mir::SourceScopeData>,
        block: &mir::BasicBlockData<'tcx>,
    ) -> Result<(), Error> {
        // Translate the statements
        let mut block_ctx = BlockTransCtx::new(self, block_id);
        for statement in &block.statements {
            trace!("statement: {:?}", statement);
            block_ctx.translate_statement(source_scopes, statement)?;
        }

        // Translate the terminator
        let terminator = block.terminator.as_ref().unwrap();
        block_ctx.translate_terminator(source_scopes, terminator)?;

        Ok(())
    }

    /// Gather all the lines that start with `//` inside the given span.
    fn translate_body_comments(
        &mut self,
        source_text: &Option<String>,
        charon_span: Span,
    ) -> Vec<(usize, Vec<String>)> {
        if let Some(body_text) = source_text {
            let mut comments = body_text
                .lines()
                // Iter through the lines of this body in reverse order.
                .rev()
                .enumerate()
                // Compute the absolute line number
                .filter_map(|(i, line)| Some((charon_span.data.end.line.checked_sub(i)?, line)))
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

    fn translate_body(
        mut self,
        mir_body: &mir::Body<'tcx>,
        source_text: &Option<String>,
    ) -> Result<Body, Error> {
        // Compute the span information
        let span = self.translate_span(&mir_body.span);

        // Initialize the local variables
        trace!("Translating the body locals");
        self.locals.arg_count = mir_body.arg_count;
        self.translate_body_locals(mir_body)?;

        // Translate the expression body
        trace!("Translating the expression body");

        // Register the start block
        let id = self.translate_basic_block_id(rustc_index::Idx::new(mir::START_BLOCK.as_usize()));
        assert!(id == START_BLOCK_ID);

        // For as long as there are blocks in the stack, translate them
        while let Some(mir_block_id) = self.blocks_stack.pop_front() {
            let mir_block = mir_body.basic_blocks.get(mir_block_id).unwrap();
            let block_id = self.translate_basic_block_id(mir_block_id);
            self.translate_basic_block(block_id, &mir_body.source_scopes, mir_block)?;
        }

        // Create the body
        let comments = self.translate_body_comments(source_text, span);
        Ok(Body::Unstructured(ExprBody {
            span,
            locals: self.locals,
            bound_body_regions: self.i_ctx.lifetime_freshener.take().unwrap().slot_count(),
            body: self.blocks.make_contiguous(),
            comments,
        }))
    }
}

impl<'tcx> BlockTransCtx<'tcx, '_, '_, '_> {
    fn missing_ptr_metadata() -> Operand {
        Operand::Const(ConstantExpr::new(
            ConstantExprKind::Opaque("Missing metadata".to_string()),
            Ty::mk_unit(),
        ))
    }

    fn apply_user_type_projection(
        &mut self,
        span: Span,
        mut ty: Ty,
        projections: &[mir::ProjectionElem<(), ()>],
    ) -> Result<Ty, Error> {
        let mut downcast = None;
        for projection in projections {
            let projection = match projection {
                mir::ProjectionElem::Deref => ProjectionElem::Deref,
                mir::ProjectionElem::Field(field, ()) => {
                    let field = self.translate_field_id(*field);
                    let TyKind::Adt(type_ref) = ty.kind() else {
                        raise_error!(self, span, "field projection on unexpected type");
                    };
                    match type_ref.as_builtin() {
                        None => ProjectionElem::Field(downcast.take(), field),
                        Some(BuiltinTy::Tuple) => ProjectionElem::Field(None, field),
                        Some(BuiltinTy::Box) if field == FieldId::ZERO => ProjectionElem::Deref,
                        _ => raise_error!(self, span, "field projection on unexpected type"),
                    }
                }
                mir::ProjectionElem::Index(()) => ProjectionElem::Index {
                    offset: Box::new(Operand::mk_const_unit()),
                    from_end: false,
                },
                mir::ProjectionElem::ConstantIndex { from_end, .. } => ProjectionElem::Index {
                    offset: Box::new(Operand::mk_const_unit()),
                    from_end: *from_end,
                },
                mir::ProjectionElem::Subslice { from_end, .. } => ProjectionElem::Subslice {
                    from: Box::new(Operand::mk_const_unit()),
                    to: Box::new(Operand::mk_const_unit()),
                    from_end: *from_end,
                },
                mir::ProjectionElem::Downcast(_, variant) => {
                    downcast = Some(self.translate_variant_id(*variant));
                    continue;
                }
                mir::ProjectionElem::OpaqueCast(()) => {
                    raise_error!(self, span, "unexpected opaque cast in user type projection");
                }
                mir::ProjectionElem::UnwrapUnsafeBinder(()) => {
                    raise_error!(
                        self,
                        span,
                        "unsupported unsafe binder in user type projection"
                    );
                }
            };
            let Some(next_ty) = projection.project_type(&self.translated, &ty) else {
                raise_error!(self, span, "invalid user type projection");
            };
            ty = next_ty;
        }
        Ok(ty)
    }

    fn translate_user_type_projection(
        &mut self,
        span: Span,
        user_ty: &mir::UserTypeProjection,
    ) -> Result<(Ty, Vec<BorrowckStatement>), Error> {
        use rustc_infer::infer::canonical::CanonicalExt;

        let annotation = self.user_type_annotations[user_ty.base].clone();
        let canonical = *annotation.user_ty;

        let mut facts = Vec::new();
        if !canonical.value.bounds.is_empty() {
            let user_ty_before_inference = match canonical.value.kind {
                ty::UserTypeKind::Ty(ty) => ty,
                ty::UserTypeKind::TypeOf(def_id, user_args)
                    if user_args.args.len() == self.tcx.generics_of(def_id).count() =>
                {
                    self.tcx
                        .type_of(def_id)
                        .instantiate(self.tcx, user_args.args)
                        .skip_normalization()
                }
                // Inherent associated type consts use a special argument format; rustc reconstructs
                // their impl arguments with inference. Their resulting type is already recorded here.
                ty::UserTypeKind::TypeOf(..) => annotation.inferred_ty,
            };

            // Rustc discards the original canonicalization values when it stores this annotation.
            // Recover just enough of that mapping to instantiate the explicit user bounds. The
            // place relation below deliberately uses `inferred_ty` directly.
            let Some(var_values) = hax::rustc::match_canonical_var_values(
                self.tcx,
                canonical.var_kinds,
                user_ty_before_inference,
                annotation.inferred_ty,
            ) else {
                raise_error!(
                    self,
                    span,
                    "could not match a user type annotation with its inferred type"
                )
            };
            let instantiated_user_ty = canonical.instantiate(self.tcx, &var_values);

            for clause in instantiated_user_ty.bounds {
                if let Some(trait_predicate) = clause.as_trait_clause() {
                    if trait_predicate.skip_binder().polarity != ty::PredicatePolarity::Positive {
                        raise_error!(self, span, "negative trait bound in a user type annotation")
                    }
                    let proof = hax::solve_trait(
                        &self.hax_state,
                        trait_predicate.map_bound(|predicate| predicate.trait_ref),
                    );
                    facts.push(BorrowckStatement::PredicateHolds(
                        self.translate_trait_proof(span, &proof)?,
                    ));
                } else if let Some(outlives) = clause.as_type_outlives_clause() {
                    let Some(ty::OutlivesClause(outlived_ty, region)) = outlives.no_bound_vars()
                    else {
                        raise_error!(self, span, "higher-ranked outlives user type bound")
                    };
                    let outlived_ty = self.translate_rustc_ty(span, &outlived_ty)?;
                    let region = self.catch_sinto(span, &region)?;
                    let region = self.translate_region(span, &region)?;
                    facts.push(BorrowckStatement::SetOutlives(outlived_ty, region));
                }
            }
        }

        // This is the type rustc itself relates the MIR place against. In particular, it has
        // already revealed local `impl Trait` types and performed type normalization.
        let ty = self.translate_rustc_ty(span, &annotation.inferred_ty)?;
        let ty = self.apply_user_type_projection(span, ty, &user_ty.projs)?;

        Ok((ty, facts))
    }

    fn translate_thread_local_ref(
        &mut self,
        span: Span,
        def_id: rustc_hir::def_id::DefId,
    ) -> Result<Rvalue, Error> {
        let args = ty::GenericArgs::empty();
        let item = hax::translate_item_ref(&self.hax_state, def_id, args);
        let global_ref = self.translate_global_decl_ref(span, &item)?;

        let ptr_ty = self.tcx.thread_local_ptr_ty(def_id);
        let ty = ptr_ty.builtin_deref(true).unwrap();
        let ty = self.translate_rustc_ty(span, &ty)?;
        let place = Place::new_global(global_ref, ty);
        match ptr_ty.kind() {
            ty::TyKind::Ref(_, _, mutability) => {
                let kind = if mutability.is_mut() {
                    BorrowKind::Mut
                } else {
                    BorrowKind::Shared
                };
                Ok(Rvalue::Ref {
                    place,
                    kind,
                    // Will be fixed by the cleanup pass `insert_ptr_metadata`.
                    ptr_metadata: Self::missing_ptr_metadata(),
                })
            }
            ty::TyKind::RawPtr(_, mutability) => {
                let kind = if mutability.is_mut() {
                    RefKind::Mut
                } else {
                    RefKind::Shared
                };
                Ok(Rvalue::RawPtr {
                    place,
                    kind,
                    // Will be fixed by the cleanup pass `insert_ptr_metadata`.
                    ptr_metadata: Self::missing_ptr_metadata(),
                })
            }
            _ => raise_error!(
                self,
                span,
                "unexpected type for thread-local reference: {ptr_ty:?}"
            ),
        }
    }

    fn translate_binaryop_kind(&mut self, _span: Span, binop: mir::BinOp) -> Result<BinOp, Error> {
        Ok(match binop {
            mir::BinOp::BitXor => BinOp::BitXor,
            mir::BinOp::BitAnd => BinOp::BitAnd,
            mir::BinOp::BitOr => BinOp::BitOr,
            mir::BinOp::Eq => BinOp::Eq,
            mir::BinOp::Lt => BinOp::Lt,
            mir::BinOp::Le => BinOp::Le,
            mir::BinOp::Ne => BinOp::Ne,
            mir::BinOp::Ge => BinOp::Ge,
            mir::BinOp::Gt => BinOp::Gt,
            mir::BinOp::Add => BinOp::Add(OverflowMode::Wrap),
            mir::BinOp::AddUnchecked => BinOp::Add(OverflowMode::UB),
            mir::BinOp::Sub => BinOp::Sub(OverflowMode::Wrap),
            mir::BinOp::SubUnchecked => BinOp::Sub(OverflowMode::UB),
            mir::BinOp::Mul => BinOp::Mul(OverflowMode::Wrap),
            mir::BinOp::MulUnchecked => BinOp::Mul(OverflowMode::UB),
            mir::BinOp::Div => BinOp::Div(OverflowMode::UB),
            mir::BinOp::Rem => BinOp::Rem(OverflowMode::UB),
            mir::BinOp::AddWithOverflow => BinOp::AddChecked,
            mir::BinOp::SubWithOverflow => BinOp::SubChecked,
            mir::BinOp::MulWithOverflow => BinOp::MulChecked,
            mir::BinOp::Shl => BinOp::Shl(OverflowMode::Wrap),
            mir::BinOp::ShlUnchecked => BinOp::Shl(OverflowMode::UB),
            mir::BinOp::Shr => BinOp::Shr(OverflowMode::Wrap),
            mir::BinOp::ShrUnchecked => BinOp::Shr(OverflowMode::UB),
            mir::BinOp::Cmp => BinOp::Cmp,
            mir::BinOp::Offset => BinOp::Offset,
        })
    }

    fn translate_place(
        &mut self,
        span: Span,
        mir_place: &mir::Place<'tcx>,
    ) -> Result<Place, Error> {
        use crate::hax::{HasBase, SInto};
        use rustc_middle::ty;

        let tcx = self.hax_state.base().tcx;
        let local_decls = self.local_decls;
        let mut place_ty: mir::PlaceTy = mir::Place::from(mir_place.local).ty(local_decls, tcx);
        let var_id = self.translate_local(&mir_place.local).unwrap();
        let mut place = self.locals.place_for_var(var_id);
        for elem in mir_place.projection.as_slice() {
            use mir::ProjectionElem::*;
            if let TyKind::Error(msg) = place.ty().kind() {
                return Err(Error {
                    span,
                    msg: msg.clone(),
                });
            }
            let projected_place_ty = place_ty.projection_ty(tcx, *elem);
            let next_place_ty = projected_place_ty.ty.sinto(&self.hax_state);
            let next_place_ty = self.translate_ty(span, &next_place_ty)?;
            let proj_elem = match elem {
                Deref => ProjectionElem::Deref,
                Field(index, _) => {
                    let TyKind::Adt(tref) = place.ty().kind() else {
                        raise_error!(
                            self,
                            span,
                            "found unexpected type in field projection: {}",
                            next_place_ty.with_ctx(&self.into_fmt())
                        )
                    };
                    let field_id = self.translate_field_id(*index);
                    match place_ty.ty.kind() {
                        ty::Adt(adt_def, _) => {
                            let variant = place_ty.variant_index;
                            let variant_id = variant.map(|id| self.translate_variant_id(id));
                            let generics = &tref.generics;
                            match tref.as_builtin() {
                                None => {
                                    assert!(
                                        ((adt_def.is_struct() || adt_def.is_union())
                                            && variant.is_none())
                                            || (adt_def.is_enum() && variant.is_some())
                                    );
                                    ProjectionElem::Field(variant_id, field_id)
                                }
                                Some(BuiltinTy::Tuple) => {
                                    assert!(generics.regions.is_empty());
                                    assert!(variant.is_none());
                                    assert!(generics.const_generics.is_empty());
                                    ProjectionElem::Field(None, field_id)
                                }
                                Some(BuiltinTy::Box) if self.t_ctx.options.treat_box_as_builtin => {
                                    // Some sanity checks
                                    assert!(generics.regions.is_empty());
                                    assert!(generics.types.len() == 2);
                                    assert!(generics.const_generics.is_empty());
                                    if field_id == FieldId::ZERO {
                                        // We pretend the pointee field is a deref.
                                        ProjectionElem::Deref
                                    } else {
                                        raise_error!(
                                            self,
                                            span,
                                            "trying to access the allocator field from Box, \
                                            but it is being treated as a builtin (without allocator)"
                                        )
                                    }
                                }
                                Some(BuiltinTy::Box) => ProjectionElem::Field(None, field_id),
                                Some(_) => {
                                    raise_error!(self, span, "Unexpected field projection")
                                }
                            }
                        }
                        ty::Tuple(_types) => ProjectionElem::Field(None, field_id),
                        // We get there when we access one of the fields of the state captured by a
                        // closure.
                        ty::Closure(..) => ProjectionElem::Field(None, field_id),
                        _ => panic!(),
                    }
                }
                Index(local) => {
                    let var_id = self.translate_local(local).unwrap();
                    let local = self.locals.place_for_var(var_id);
                    let offset = Operand::Copy(local);
                    ProjectionElem::Index {
                        offset: Box::new(offset),
                        from_end: false,
                    }
                }
                &ConstantIndex {
                    offset, from_end, ..
                } => {
                    let offset =
                        Operand::Const(ScalarValue::mk_usize(offset as u128).to_constant());
                    ProjectionElem::Index {
                        offset: Box::new(offset),
                        from_end,
                    }
                }
                &Subslice { from, to, from_end } => {
                    let from = Operand::Const(ScalarValue::mk_usize(from as u128).to_constant());
                    let to = Operand::Const(ScalarValue::mk_usize(to as u128).to_constant());
                    ProjectionElem::Subslice {
                        from: Box::new(from),
                        to: Box::new(to),
                        from_end,
                    }
                }
                OpaqueCast(..) => {
                    raise_error!(self, span, "Unexpected ProjectionElem::OpaqueCast");
                }
                Downcast { .. } => {
                    // We keep the same `Place`, the variant is tracked in the `PlaceTy` and we can
                    // access it next loop iteration.
                    place_ty = projected_place_ty;
                    continue;
                }
                UnwrapUnsafeBinder { .. } => {
                    raise_error!(self, span, "unsupported feature: unsafe binders");
                }
            };
            place = place.project(proj_elem, next_place_ty);
            place_ty = projected_place_ty;
        }
        Ok(place)
    }

    /// Translate an operand
    fn translate_operand(
        &mut self,
        span: Span,
        operand: &mir::Operand<'tcx>,
    ) -> Result<Operand, Error> {
        Ok(match operand {
            mir::Operand::Copy(place) => {
                let p = self.translate_place(span, place)?;
                Operand::Copy(p)
            }
            mir::Operand::Move(place) => {
                let p = self.translate_place(span, place)?;
                Operand::Move(p)
            }
            mir::Operand::Constant(const_op) => {
                let const_op = self.catch_sinto(span, &const_op)?;
                match &const_op.kind {
                    hax::ConstOperandKind::Value(constant) => {
                        let constant = self.translate_constant_expr(span, constant)?;
                        Operand::Const(constant)
                    }
                    hax::ConstOperandKind::Promoted(item) => {
                        // A promoted constant that could not be evaluated.
                        let global_ref = self.translate_global_decl_ref(span, item)?;
                        let constant = ConstantExpr::new(
                            ConstantExprKind::Global(global_ref),
                            self.translate_ty(span, &const_op.ty)?,
                        );
                        Operand::Const(constant)
                    }
                }
            }
            mir::Operand::RuntimeChecks(check) => {
                let op = match check {
                    mir::RuntimeChecks::UbChecks => NullOp::UbChecks,
                    mir::RuntimeChecks::OverflowChecks => NullOp::OverflowChecks,
                    mir::RuntimeChecks::ContractChecks => NullOp::ContractChecks,
                };
                let local = self.locals.new_var(None, Ty::mk_bool());
                self.statements.push(Statement {
                    span,
                    kind: StatementKind::StorageLive(local.as_local().unwrap()),
                    comments_before: vec![],
                });
                self.statements.push(Statement {
                    span,
                    kind: StatementKind::Assign(
                        local.clone(),
                        Rvalue::NullaryOp(op, Ty::mk_bool()),
                    ),
                    comments_before: vec![],
                });
                Operand::Move(local)
            }
        })
    }

    /// Translate an rvalue
    fn translate_mir_rvalue(
        &mut self,
        span: Span,
        rvalue: &mir::Rvalue<'tcx>,
        tgt_ty: &Ty,
    ) -> Result<Rvalue, Error> {
        match rvalue {
            mir::Rvalue::Use(operand, retag) => {
                let retag = match retag {
                    mir::WithRetag::Yes => WithRetag::Yes,
                    mir::WithRetag::No => WithRetag::No,
                };
                Ok(Rvalue::Use(self.translate_operand(span, operand)?, retag))
            }
            mir::Rvalue::CopyForDeref(place) => {
                // According to the documentation, it seems to be an optimisation
                // for drop elaboration. We treat it as a regular copy.
                let place = self.translate_place(span, place)?;
                Ok(Rvalue::Use(Operand::Copy(place), WithRetag::No))
            }
            mir::Rvalue::Repeat(operand, cnst) => {
                let c = self.translate_ty_constant_expr(span, cnst)?;
                let op = self.translate_operand(span, operand)?;
                let ty = op.ty().clone();
                // Remark: we could desugar this into a function call later.
                Ok(Rvalue::Repeat(op, ty, c))
            }
            mir::Rvalue::Ref(_region, borrow_kind, place) => {
                let place = self.translate_place(span, place)?;
                let borrow_kind = self.translate_borrow_kind(*borrow_kind);
                Ok(Rvalue::Ref {
                    place,
                    kind: borrow_kind,
                    // Will be fixed by the cleanup pass `insert_ptr_metadata`.
                    ptr_metadata: Self::missing_ptr_metadata(),
                })
            }
            mir::Rvalue::RawPtr(mtbl, place) => {
                let mtbl = match mtbl {
                    mir::RawPtrKind::Mut => RefKind::Mut,
                    mir::RawPtrKind::Const => RefKind::Shared,
                    mir::RawPtrKind::FakeForPtrMetadata => RefKind::Shared,
                };
                let place = self.translate_place(span, place)?;
                Ok(Rvalue::RawPtr {
                    place,
                    kind: mtbl,
                    // Will be fixed by the cleanup pass `insert_ptr_metadata`.
                    ptr_metadata: Self::missing_ptr_metadata(),
                })
            }
            mir::Rvalue::Cast(cast_kind, mir_operand, rust_tgt_ty) => {
                let op_ty = mir_operand.ty(self.local_decls, self.tcx);
                let tgt_ty = self.translate_rustc_ty(span, rust_tgt_ty)?;

                // Translate the operand
                let mut operand = self.translate_operand(span, mir_operand)?;
                let src_ty = operand.ty().clone();

                let cast_kind = match cast_kind {
                    mir::CastKind::IntToInt
                    | mir::CastKind::IntToFloat
                    | mir::CastKind::FloatToInt
                    | mir::CastKind::FloatToFloat => {
                        let tgt_ty = *tgt_ty.kind().as_literal().unwrap();
                        let src_ty = *src_ty.kind().as_literal().unwrap();
                        CastKind::Scalar(src_ty, tgt_ty)
                    }
                    mir::CastKind::PtrToPtr
                    | mir::CastKind::PointerCoercion(
                        ty::adjustment::PointerCoercion::MutToConstPointer,
                        ..,
                    )
                    | mir::CastKind::PointerCoercion(
                        ty::adjustment::PointerCoercion::ArrayToPointer,
                        ..,
                    )
                    | mir::CastKind::FnPtrToPtr
                    | mir::CastKind::PointerExposeProvenance
                    | mir::CastKind::PointerWithExposedProvenance => {
                        CastKind::RawPtr(src_ty, tgt_ty)
                    }
                    mir::CastKind::PointerCoercion(
                        ty::adjustment::PointerCoercion::ClosureFnPointer(_),
                        ..,
                    ) => {
                        let hax_op_ty: hax::Ty = self.catch_sinto(span, &op_ty)?;
                        // We model casts of closures to function pointers by generating a new
                        // function item without the closure's state, that calls the actual closure.
                        let hax::TyKind::Closure(closure, ..) = hax_op_ty.kind() else {
                            unreachable!("Non-closure type in PointerCoercion::ClosureFnPointer");
                        };
                        let fn_ref: RegionBinder<FunDeclRef> =
                            self.translate_stateless_closure_as_fn_ref(span, closure)?;
                        let fn_ptr_bound: RegionBinder<FnPtr> = fn_ref.map(FunDeclRef::into);
                        let fn_ptr: FnPtr = self.erase_region_binder(fn_ptr_bound.clone());
                        let src_ty = TyKind::FnDef(fn_ptr_bound).into_ty();
                        operand = Operand::Const(ConstantExpr::new(
                            ConstantExprKind::FnDef(fn_ptr),
                            src_ty.clone(),
                        ));
                        CastKind::FnPtr(src_ty, tgt_ty)
                    }
                    mir::CastKind::PointerCoercion(
                        ty::adjustment::PointerCoercion::UnsafeFnPointer
                        | ty::adjustment::PointerCoercion::ReifyFnPointer(_),
                        ..,
                    ) => CastKind::FnPtr(src_ty, tgt_ty),
                    mir::CastKind::Transmute | mir::CastKind::BoxDerefTransmute => {
                        CastKind::Transmute(src_ty, tgt_ty)
                    }
                    // TODO
                    mir::CastKind::Subtype => CastKind::Transmute(src_ty, tgt_ty),
                    mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, ..) => {
                        let meta =
                            hax::compute_unsizing_metadata(&self.hax_state, op_ty, *rust_tgt_ty);
                        let meta = self.translate_unsizing_metadata(span, meta)?;
                        CastKind::Unsize(src_ty, tgt_ty.clone(), meta)
                    }
                };
                let unop = UnOp::Cast(cast_kind);
                Ok(Rvalue::UnaryOp(unop, operand))
            }
            mir::Rvalue::BinaryOp(binop, (left, right)) => Ok(Rvalue::BinaryOp(
                self.translate_binaryop_kind(span, *binop)?,
                self.translate_operand(span, left)?,
                self.translate_operand(span, right)?,
            )),
            mir::Rvalue::UnaryOp(unop, operand) => {
                let operand = self.translate_operand(span, operand)?;
                let unop = match unop {
                    mir::UnOp::Not => UnOp::Not,
                    mir::UnOp::Neg => UnOp::Neg(OverflowMode::Wrap),
                    mir::UnOp::PtrMetadata => match operand {
                        Operand::Copy(p) | Operand::Move(p) => {
                            return Ok(Rvalue::Use(
                                Operand::Copy(
                                    p.project(ProjectionElem::PtrMetadata, tgt_ty.clone()),
                                ),
                                WithRetag::No,
                            ));
                        }
                        Operand::Const(_) => {
                            panic!("unexpected metadata operand")
                        }
                    },
                };
                Ok(Rvalue::UnaryOp(unop, operand))
            }
            mir::Rvalue::Discriminant(place) => {
                let place = self.translate_place(span, place)?;
                Ok(Rvalue::Discriminant(place))
            }
            mir::Rvalue::Aggregate(aggregate_kind, operands) => {
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
                    .iter()
                    .map(|op| self.translate_operand(span, op))
                    .try_collect()?;
                match aggregate_kind {
                    mir::AggregateKind::Array(ty) => {
                        let t_ty = self.translate_rustc_ty(span, ty)?;
                        let c = ConstantExpr::mk_usize(operands_t.len() as u128);
                        Ok(Rvalue::Aggregate(AggregateKind::Array(t_ty, c), operands_t))
                    }
                    mir::AggregateKind::Tuple => {
                        let tys = operands.iter().map(|op| op.ty(self.local_decls, self.tcx));
                        let ty = ty::Ty::new_tup_from_iter(self.tcx, tys);
                        let ty = self.translate_rustc_ty(span, &ty)?;
                        let tref = ty.as_adt().unwrap().clone();
                        Ok(Rvalue::Aggregate(
                            AggregateKind::Adt(tref, None, None),
                            operands_t,
                        ))
                    }
                    mir::AggregateKind::Adt(def_id, variant_idx, generics, _, field_index) => {
                        use ty::AdtKind;
                        trace!("{:?}", rvalue);

                        let adt_kind = self.tcx.adt_def(*def_id).adt_kind();
                        let item = hax::translate_item_ref(&self.hax_state, *def_id, generics);
                        let tref = self.translate_type_decl_ref(span, &item)?;
                        let variant_id = match adt_kind {
                            AdtKind::Struct | AdtKind::Union => None,
                            AdtKind::Enum => Some(self.translate_variant_id(*variant_idx)),
                        };
                        let field_id = match adt_kind {
                            AdtKind::Struct | AdtKind::Enum => None,
                            AdtKind::Union => Some(self.translate_field_id(field_index.unwrap())),
                        };

                        let akind = AggregateKind::Adt(tref, variant_id, field_id);
                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    mir::AggregateKind::Closure(def_id, generics) => {
                        let args = hax::ClosureArgs::sfrom(&self.hax_state, *def_id, generics);
                        let tref = self.translate_closure_type_ref(span, &args)?;
                        let akind = AggregateKind::Adt(tref, None, None);
                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    mir::AggregateKind::RawPtr(ty, mutability) => {
                        // TODO: replace with a call to `ptr::from_raw_parts`.
                        let t_ty = self.translate_rustc_ty(span, ty)?;
                        let mutability = if mutability.is_mut() {
                            RefKind::Mut
                        } else {
                            RefKind::Shared
                        };

                        let akind = AggregateKind::RawPtr(t_ty, mutability);

                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    mir::AggregateKind::Coroutine(..)
                    | mir::AggregateKind::CoroutineClosure(..) => {
                        raise_error!(self, span, "Coroutines are not supported");
                    }
                }
            }
            mir::Rvalue::ThreadLocalRef(def_id) => self.translate_thread_local_ref(span, *def_id),
            mir::Rvalue::WrapUnsafeBinder { .. } => {
                raise_error!(
                    self,
                    span,
                    "charon does not support unsafe lifetime binders"
                );
            }
            mir::Rvalue::Reborrow(..) => {
                raise_error!(
                    self,
                    span,
                    "charon does not support reborrow rvalues (for Reborrow traits)"
                );
            }
        }
    }

    /// Translate a statement.
    fn translate_statement(
        &mut self,
        source_scopes: &rustc_index::IndexVec<mir::SourceScope, mir::SourceScopeData>,
        statement: &mir::Statement<'tcx>,
    ) -> Result<(), Error> {
        trace!("About to translate statement (MIR) {:?}", statement);
        let span = self.translate_span_from_source_info(source_scopes, &statement.source_info);

        let kind: Option<StatementKind> = match &statement.kind {
            mir::StatementKind::Assign((place, rvalue)) => {
                let t_place = self.translate_place(span, place)?;
                let t_rvalue = self.translate_mir_rvalue(span, rvalue, t_place.ty())?;
                Some(StatementKind::Assign(t_place, t_rvalue))
            }
            mir::StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                let t_place = self.translate_place(span, place)?;
                let variant_id = self.translate_variant_id(*variant_index);
                Some(StatementKind::SetDiscriminant(t_place, variant_id))
            }
            mir::StatementKind::StorageLive(local) => {
                let var_id = self.translate_local(local).unwrap();
                Some(StatementKind::StorageLive(var_id))
            }
            mir::StatementKind::StorageDead(local) => {
                let var_id = self.translate_local(local).unwrap();
                Some(StatementKind::StorageDead(var_id))
            }
            mir::StatementKind::Intrinsic(mir::NonDivergingIntrinsic::Assume(op)) => {
                let op = self.translate_operand(span, op)?;
                self.translate_intrinsic_call(
                    span,
                    sym::assume,
                    ty::GenericArgs::empty(),
                    vec![op],
                )?;
                None
            }
            mir::StatementKind::Intrinsic(mir::NonDivergingIntrinsic::CopyNonOverlapping(
                mir::CopyNonOverlapping { src, dst, count },
            )) => {
                let pointee_ty = src
                    .ty(self.local_decls, self.tcx)
                    .builtin_deref(true)
                    .unwrap();
                let generic_args = self.tcx.mk_args(&[pointee_ty.into()]);
                let src = self.translate_operand(span, src)?;
                let dst = self.translate_operand(span, dst)?;
                let count = self.translate_operand(span, count)?;
                self.translate_intrinsic_call(
                    span,
                    sym::copy_nonoverlapping,
                    generic_args,
                    vec![src, dst, count],
                )?;
                None
            }
            mir::StatementKind::PlaceMention(place) => {
                let place = self.translate_place(span, place)?;
                // We only translate this for places with projections, as
                // no UB can arise from simply mentioning a local variable.
                if place.is_local() {
                    None
                } else {
                    Some(StatementKind::PlaceMention(place))
                }
            }
            mir::StatementKind::FakeRead((_, place)) => {
                let place = self.translate_place(span, place)?;
                Some(StatementKind::Borrowck(BorrowckStatement::FakeRead(place)))
            }
            mir::StatementKind::AscribeUserType((place, user_ty), variance) => {
                let variance = match variance {
                    ty::Variance::Covariant => Variance::Covariant,
                    ty::Variance::Invariant => Variance::Invariant,
                    ty::Variance::Contravariant => Variance::Contravariant,
                    // Does nothing so we discard it.
                    ty::Variance::Bivariant => return Ok(()),
                };
                let place = self.translate_place(span, place)?;
                let (ty, facts) = self.translate_user_type_projection(span, user_ty)?;
                self.statements.push(Statement::new(
                    span,
                    StatementKind::Borrowck(BorrowckStatement::SetType {
                        place,
                        ty,
                        variance,
                    }),
                ));
                self.statements.extend(
                    facts
                        .into_iter()
                        .map(|fact| Statement::new(span, StatementKind::Borrowck(fact))),
                );
                None
            }
            // Used for coverage instrumentation.
            mir::StatementKind::Coverage(_) => None,
            // Used in the interpreter to check that const code doesn't run for too long or even
            // indefinitely.
            mir::StatementKind::ConstEvalCounter => None,
            // Semantically equivalent to `Nop`, used only for rustc lints.
            mir::StatementKind::BackwardIncompatibleDropHint { .. } => None,
            mir::StatementKind::Nop => None,
        };

        let Some(kind) = kind else {
            return Ok(());
        };
        self.statements.push(Statement::new(span, kind));
        Ok(())
    }

    /// Translate a call to a non-diverging intrinsic.
    fn translate_intrinsic_call(
        &mut self,
        span: Span,
        name: Symbol,
        generic_args: ty::GenericArgsRef<'tcx>,
        args: Vec<Operand>,
    ) -> Result<(), Error> {
        // Sadly rustc doesn't expose a Symbol -> DefId map for intrinsics.
        let path = NamePattern::parse(&format!("core::intrinsics::{name}")).unwrap();
        let def_id = self
            .resolve_path(span, &path, true)?
            .into_iter()
            .exactly_one()
            .unwrap();
        assert!(self.tcx.is_intrinsic(def_id, name));
        let item = hax::ItemRef::translate(self.hax_state_with_id(), def_id, generic_args);
        let func =
            FnOperand::Regular(self.translate_fn_ptr(span, &item, TransItemSourceKind::Fun)?);
        let dest = self.locals.new_var(None, Ty::mk_unit());
        self.push_nounwind_call(span, Call { func, args, dest });
        Ok(())
    }

    /// Translate a terminator
    fn translate_terminator(
        mut self,
        source_scopes: &rustc_index::IndexVec<mir::SourceScope, mir::SourceScopeData>,
        terminator: &mir::Terminator<'tcx>,
    ) -> Result<(), Error> {
        trace!("About to translate terminator (MIR) {:?}", terminator);
        let span = self.translate_span_from_source_info(source_scopes, &terminator.source_info);

        // Translate the terminator
        use mir::TerminatorKind;
        let kind: ullbc_ast::TerminatorKind = match &terminator.kind {
            TerminatorKind::Goto { target } => {
                let target = self.translate_basic_block_id(*target);
                ullbc_ast::TerminatorKind::Goto { target }
            }
            TerminatorKind::SwitchInt { discr, targets, .. } => {
                let discr = self.translate_operand(span, discr)?;
                let (data, branches) = self.translate_switch_targets(span, discr, targets)?;
                ullbc_ast::TerminatorKind::Switch { data, branches }
            }
            TerminatorKind::UnwindResume => ullbc_ast::TerminatorKind::UnwindResume,
            TerminatorKind::UnwindTerminate { .. } => {
                ullbc_ast::TerminatorKind::Abort(AbortKind::UnwindTerminate)
            }
            TerminatorKind::Return => ullbc_ast::TerminatorKind::Return,
            // A MIR `Unreachable` terminator indicates undefined behavior of the rust abstract
            // machine.
            TerminatorKind::Unreachable => {
                ullbc_ast::TerminatorKind::Abort(AbortKind::UndefinedBehavior)
            }
            TerminatorKind::Drop {
                place,
                target,
                unwind,
                ..
            } => self.translate_drop(span, place, target, unwind)?,
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => self.translate_function_call(span, func, args, destination, target, unwind)?,
            TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                unwind,
            } => {
                let on_unwind = self.translate_unwind_action(span, unwind);
                let kind = self.translate_assert_kind(span, msg)?;
                let assert = Assert {
                    cond: self.translate_operand(span, cond)?,
                    expected: *expected,
                    check_kind: Some(kind),
                };
                let target = self.translate_basic_block_id(*target);
                ullbc_ast::TerminatorKind::Assert {
                    assert,
                    target,
                    on_unwind,
                }
            }
            TerminatorKind::FalseEdge {
                real_target,
                imaginary_target: _,
            } => {
                // False edges are used to make the borrow checker a bit conservative.
                // We translate them as Gotos.
                // Also note that they are used in some passes, and not in some others
                // (they are present in mir_promoted, but not mir_optimized).
                let target = self.translate_basic_block_id(*real_target);
                ullbc_ast::TerminatorKind::Goto { target }
            }
            TerminatorKind::FalseUnwind {
                real_target,
                unwind: _,
            } => {
                // We consider this to be a goto
                let target = self.translate_basic_block_id(*real_target);
                ullbc_ast::TerminatorKind::Goto { target }
            }
            TerminatorKind::InlineAsm {
                template,
                targets,
                unwind,
                ..
            } => {
                let asm = rustc_ast::ast::InlineAsmTemplatePiece::to_string(template);
                let targets = targets
                    .iter()
                    .map(|target| self.translate_basic_block_id(*target))
                    .collect();
                let on_unwind = self.translate_unwind_action(span, unwind);
                ullbc_ast::TerminatorKind::InlineAsm {
                    asm,
                    targets,
                    on_unwind,
                }
            }
            TerminatorKind::CoroutineDrop
            | TerminatorKind::TailCall { .. }
            | TerminatorKind::Yield { .. } => {
                raise_error!(self, span, "Unsupported terminator: {:?}", terminator.kind);
            }
        };

        self.finish_current_block(Terminator::new(span, kind));
        Ok(())
    }

    /// Translate switch targets
    fn translate_switch_targets(
        &mut self,
        span: Span,
        discr: Operand,
        targets: &mir::SwitchTargets,
    ) -> Result<(SwitchData, IndexVec<BranchId, BlockId>), Error> {
        // Convert all the test values to the proper values.
        let otherwise = targets.otherwise();
        let switch_ty = discr.ty();
        let switch_literal_ty = *switch_ty.as_literal().unwrap();
        let mut branch_targets: IndexVec<BranchId, BlockId> = IndexVec::new();
        let mut target_to_branch: SeqHashMap<BlockId, BranchId> = SeqHashMap::new();
        let mut switch_branches = Vec::with_capacity(targets.iter().count());

        // Keep the historical true-then-false traversal order for boolean switches.
        let bool_fallback = (switch_literal_ty == LiteralTy::Bool).then(|| {
            let target = self.translate_basic_block_id(otherwise);
            *target_to_branch
                .entry(target)
                .or_insert_with(|| branch_targets.push(target))
        });

        for (bits, target) in targets.iter() {
            let Some(literal) = Literal::from_bits(&switch_literal_ty, bits) else {
                raise_error!(self, span, "Can't match on type {switch_literal_ty}")
            };
            let target = self.translate_basic_block_id(target);
            let branch_id = *target_to_branch
                .entry(target)
                .or_insert_with(|| branch_targets.push(target));
            let value = ConstantExpr::new(ConstantExprKind::Literal(literal), switch_ty.clone());
            switch_branches.push((value, branch_id));
        }

        let fallback = bool_fallback.unwrap_or_else(|| {
            let target = self.translate_basic_block_id(otherwise);
            *target_to_branch
                .entry(target)
                .or_insert_with(|| branch_targets.push(target))
        });
        let data = SwitchData {
            scrutinee: SwitchScrutinee::Value(discr),
            branches: switch_branches,
            fallback: Some(fallback),
        };
        Ok((data, branch_targets))
    }

    /// Translate a function call statement.
    /// Note that `body` is the body of the function being translated, not of the
    /// function referenced in the function call: we need it in order to translate
    /// the blocks we go to after the function call returns.
    #[allow(clippy::too_many_arguments)]
    fn translate_function_call(
        &mut self,
        span: Span,
        func: &mir::Operand<'tcx>,
        args: &[hax::Spanned<mir::Operand<'tcx>>],
        destination: &mir::Place<'tcx>,
        target: &Option<mir::BasicBlock>,
        unwind: &mir::UnwindAction,
    ) -> Result<TerminatorKind, Error> {
        let tcx = self.tcx;
        let op_ty = func.ty(self.local_decls, tcx);
        // There are two cases, depending on whether this is a "regular"
        // call to a top-level function identified by its id, or if we
        // are using a local function pointer (i.e., the operand is a "move").
        let lval = self.translate_place(span, destination)?;
        let on_unwind = self.translate_unwind_action(span, unwind);
        // Translate the function operand.
        let fn_operand = match op_ty.kind() {
            ty::TyKind::FnDef(def_id, generics) => {
                // The type of the value is one of the singleton types that corresponds to each function,
                // which is enough information.
                let generics = generics.no_bound_vars().expect("bound variables in FnDef");
                let item = &hax::translate_item_ref(&self.hax_state, *def_id, generics);
                trace!("func: {:?}", item.def_id);
                let fun_def = self.hax_def(item)?;
                let item_src =
                    TransItemSource::from_item(item, TransItemSourceKind::Fun, self.monomorphize());
                let name = self.t_ctx.translate_name(&item_src)?;
                let panic_lang_items = &["panic", "panic_fmt", "begin_panic"];
                let panic_names = &[&["core", "panicking", "assert_failed"], EXPLICIT_PANIC_NAME];

                if fun_def
                    .lang_item
                    .as_ref()
                    .is_some_and(|lang_it| panic_lang_items.iter().contains(&lang_it.as_str()))
                    || panic_names.iter().any(|panic| name.equals_ref_name(panic))
                {
                    // If the call is `panic!`, then the target is `None`.
                    // I don't know in which other cases it can be `None`.
                    assert!(target.is_none());
                    // We ignore the arguments
                    // TODO: shouldn't we do something with the unwind edge?
                    return Ok(TerminatorKind::Abort(AbortKind::Panic(Some(name))));
                } else {
                    let fn_ptr = self.translate_fn_ptr(span, item, TransItemSourceKind::Fun)?;
                    FnOperand::Regular(fn_ptr)
                }
            }
            _ => {
                // Call to a function pointer.
                let op = self.translate_operand(span, func)?;
                FnOperand::Dynamic(op)
            }
        };
        let args = self.translate_arguments(span, args)?;
        let call = Call {
            func: fn_operand,
            args,
            dest: lval,
        };

        let target = match target {
            Some(target) => self.translate_basic_block_id(*target),
            None => {
                let abort =
                    Terminator::new(span, TerminatorKind::Abort(AbortKind::UndefinedBehavior));
                self.blocks.push(abort.into_block())
            }
        };

        Ok(TerminatorKind::Call {
            call,
            target,
            on_unwind,
        })
    }

    /// Translate a drop terminator
    #[allow(clippy::too_many_arguments)]
    fn translate_drop(
        &mut self,
        span: Span,
        place: &mir::Place<'tcx>,
        target: &mir::BasicBlock,
        unwind: &mir::UnwindAction,
    ) -> Result<TerminatorKind, Error> {
        let place_ty = place.ty(self.local_decls, self.tcx).ty;
        let fn_ptr = self.translate_drop_glue_method_call(span, place_ty)?;
        let place = self.translate_place(span, place)?;
        let target = self.translate_basic_block_id(*target);
        let on_unwind = self.translate_unwind_action(span, unwind);

        Ok(TerminatorKind::Drop {
            kind: self.drop_kind,
            place,
            fn_ptr,
            target,
            on_unwind,
        })
    }

    // construct unwind block for the terminators
    fn translate_unwind_action(&mut self, span: Span, unwind: &mir::UnwindAction) -> BlockId {
        match unwind {
            mir::UnwindAction::Continue => {
                let unwind_continue = Terminator::new(span, TerminatorKind::UnwindResume);
                self.blocks.push(unwind_continue.into_block())
            }
            mir::UnwindAction::Unreachable => {
                let abort =
                    Terminator::new(span, TerminatorKind::Abort(AbortKind::UndefinedBehavior));
                self.blocks.push(abort.into_block())
            }
            mir::UnwindAction::Terminate(..) => {
                let abort =
                    Terminator::new(span, TerminatorKind::Abort(AbortKind::UnwindTerminate));
                self.blocks.push(abort.into_block())
            }
            mir::UnwindAction::Cleanup(bb) => self.translate_basic_block_id(*bb),
        }
    }

    fn translate_assert_kind(
        &mut self,
        span: Span,
        kind: &mir::AssertKind<mir::Operand<'tcx>>,
    ) -> Result<BuiltinAssertKind, Error> {
        match kind {
            mir::AssertKind::BoundsCheck { len, index } => {
                let len = self.translate_operand(span, len)?;
                let index = self.translate_operand(span, index)?;
                Ok(BuiltinAssertKind::BoundsCheck { len, index })
            }
            mir::AssertKind::Overflow(binop, left, right) => {
                let binop = self.translate_binaryop_kind(span, *binop)?;
                let left = self.translate_operand(span, left)?;
                let right = self.translate_operand(span, right)?;
                Ok(BuiltinAssertKind::Overflow(binop, left, right))
            }
            mir::AssertKind::OverflowNeg(operand) => {
                let operand = self.translate_operand(span, operand)?;
                Ok(BuiltinAssertKind::OverflowNeg(operand))
            }
            mir::AssertKind::DivisionByZero(operand) => {
                let operand = self.translate_operand(span, operand)?;
                Ok(BuiltinAssertKind::DivisionByZero(operand))
            }
            mir::AssertKind::RemainderByZero(operand) => {
                let operand = self.translate_operand(span, operand)?;
                Ok(BuiltinAssertKind::RemainderByZero(operand))
            }
            mir::AssertKind::MisalignedPointerDereference { required, found } => {
                let required = self.translate_operand(span, required)?;
                let found = self.translate_operand(span, found)?;
                Ok(BuiltinAssertKind::MisalignedPointerDereference { required, found })
            }
            mir::AssertKind::NullPointerDereference => {
                Ok(BuiltinAssertKind::NullPointerDereference)
            }
            mir::AssertKind::NullReferenceConstructed => {
                Ok(BuiltinAssertKind::NullReferenceCreated)
            }
            mir::AssertKind::InvalidEnumConstruction(operand) => {
                let operand = self.translate_operand(span, operand)?;
                Ok(BuiltinAssertKind::InvalidEnumConstruction(operand))
            }
            mir::AssertKind::ResumedAfterDrop(..)
            | mir::AssertKind::ResumedAfterPanic(..)
            | mir::AssertKind::ResumedAfterReturn(..) => {
                raise_error!(self, span, "Coroutines are not supported");
            }
        }
    }

    /// Evaluate function arguments in a context, and return the list of computed
    /// values.
    fn translate_arguments(
        &mut self,
        span: Span,
        args: &[hax::Spanned<mir::Operand<'tcx>>],
    ) -> Result<Vec<Operand>, Error> {
        let mut t_args: Vec<Operand> = Vec::new();
        for arg in args.iter().map(|x| &x.node) {
            // Translate
            let op = self.translate_operand(span, arg)?;
            t_args.push(op);
        }
        Ok(t_args)
    }
}

impl<'a> IntoFormatter for &'a BodyTransCtx<'_, '_, '_> {
    type C = FmtCtx<'a>;
    fn into_fmt(self) -> Self::C {
        FmtCtx {
            local_names: Some(compute_local_names(&self.locals)),
            ..self.i_ctx.into_fmt()
        }
    }
}
