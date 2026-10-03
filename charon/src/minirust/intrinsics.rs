//! Functions synthesized to implement intrinsics and start the program.

use super::*;
use itertools::Itertools;

pub(super) struct FunctionBuilder {
    locals: Vec<mini::Type>,
    arg_count: usize,
    blocks: Vec<Option<mini::BasicBlock>>,
    calling_convention: mini::CallingConvention,
}

impl FunctionBuilder {
    pub(super) fn new<T: mini::Target>(
        ctx: &TranslateCtx<'_, T>,
        span: Span,
        signature: &FunSig,
    ) -> Result<Self> {
        let locals = std::iter::once(&signature.output)
            .chain(&signature.inputs)
            .map(|ty| ctx.ty(span, ty))
            .try_collect()?;
        Ok(Self {
            locals,
            arg_count: signature.inputs.len(),
            blocks: Vec::new(),
            calling_convention: ctx.calling_convention(span, &signature.abi)?,
        })
    }

    pub(super) fn return_local(&self) -> mini::LocalName {
        mini::LocalName(name(0))
    }

    pub(super) fn argument(&self, index: usize) -> mini::LocalName {
        assert!(index < self.arg_count);
        mini::LocalName(name((index + 1) as u32))
    }

    pub(super) fn add_local(&mut self, ty: mini::Type) -> mini::LocalName {
        let name = mini::LocalName(name(self.locals.len() as u32));
        self.locals.push(ty);
        name
    }

    pub(super) fn declare_block(&mut self) -> mini::BbName {
        let name = mini::BbName(name(self.blocks.len() as u32));
        self.blocks.push(None);
        name
    }

    pub(super) fn set_block(&mut self, name: mini::BbName, block: mini::BasicBlock) {
        assert!(
            self.blocks[name.0.get_internal() as usize]
                .replace(block)
                .is_none(),
            "MiniRust block was defined twice"
        );
    }

    pub(super) fn finish(self) -> mini::Function {
        let blocks = self
            .blocks
            .into_iter()
            .map(|block| block.expect("MiniRust block was declared but never defined"))
            .collect_vec();
        let mut function = mb::function(mb::Ret::Yes, self.arg_count, &self.locals, &blocks);
        function.calling_convention = self.calling_convention;
        function
    }
}

pub(super) enum UnwindSource {
    ExplicitPayload,
    OpaquePayload,
}

impl<T: mini::Target> TranslateCtx<'_, T> {
    /// Lowers this function to an intrinsic if we recognize it as such. Otherwise return `None`.
    pub(super) fn lower_intrinsic(&self, fdecl: &FunDecl) -> Result<Option<mini::Function>> {
        let span = fdecl.item_meta.span;
        let function = if let [PathElem::Ident(krate, _), PathElem::Ident(item, _)] =
            fdecl.item_meta.name.as_slice_uninstantiated()
            && krate == "intrinsics"
        {
            // Recognize the intrinsics used by MiniRust's `minimize` test suite.
            let intrinsic_op = match item.as_str() {
                "print" => mini::IntrinsicOp::PrintStdout,
                "eprint" => mini::IntrinsicOp::PrintStderr,
                "exit" => mini::IntrinsicOp::Exit,
                "allocate" => mini::IntrinsicOp::Allocate,
                "deallocate" => mini::IntrinsicOp::Deallocate,
                "spawn" => mini::IntrinsicOp::Spawn,
                "join" => mini::IntrinsicOp::Join,
                "create_lock" => mini::IntrinsicOp::Lock(mini::IntrinsicLockOp::Create),
                "acquire" => mini::IntrinsicOp::Lock(mini::IntrinsicLockOp::Acquire),
                "release" => mini::IntrinsicOp::Lock(mini::IntrinsicLockOp::Release),
                "atomic_store" => mini::IntrinsicOp::AtomicStore,
                "atomic_load" => mini::IntrinsicOp::AtomicLoad,
                "compare_exchange" => mini::IntrinsicOp::AtomicCompareExchange,
                "atomic_fetch_add" => mini::IntrinsicOp::AtomicFetchAndOp(mini::IntBinOp::Add),
                "atomic_fetch_sub" => mini::IntrinsicOp::AtomicFetchAndOp(mini::IntBinOp::Sub),
                _ => raise!(span, "unknown MiniRust test intrinsic `{item}`"),
            };
            self.make_intrinsic_function(span, fdecl, intrinsic_op)?
        } else if let Some(lang_item) = &fdecl.item_meta.lang_item {
            match lang_item {
                LangItem::PanicFmt => {
                    self.make_unwind_function(span, fdecl, UnwindSource::OpaquePayload)?
                }
                _ => return Ok(None),
            }
        } else {
            match &fdecl.body {
                Body::Extern(name) => match name.as_str() {
                    "minirust_print" => {
                        self.make_intrinsic_function(span, fdecl, mini::IntrinsicOp::PrintStdout)?
                    }
                    "minirust_start_unwind" => {
                        self.make_unwind_function(span, fdecl, UnwindSource::ExplicitPayload)?
                    }
                    "panic_impl" => {
                        self.make_unwind_function(span, fdecl, UnwindSource::OpaquePayload)?
                    }
                    _ => return Ok(None),
                },
                Body::Intrinsic { name, .. } => match name.as_str() {
                    "abort" => {
                        self.make_intrinsic_function(span, fdecl, mini::IntrinsicOp::Abort)?
                    }
                    "assume" => {
                        self.make_intrinsic_function(span, fdecl, mini::IntrinsicOp::Assume)?
                    }
                    "raw_eq" => {
                        self.make_intrinsic_function(span, fdecl, mini::IntrinsicOp::RawEq)?
                    }
                    "catch_unwind" => self.make_catch_unwind_function(span, fdecl)?,
                    "size_of_val" => self.make_layout_of_val_function(span, fdecl, false)?,
                    "align_of_val" => self.make_layout_of_val_function(span, fdecl, true)?,
                    "cold_path" => self.make_cold_path_function(span, fdecl)?,
                    "arith_offset" => self.make_arith_offset_function(span, fdecl)?,
                    "ptr_offset_from" => self.make_ptr_offset_from_function(span, fdecl, false)?,
                    "ptr_offset_from_unsigned" => {
                        self.make_ptr_offset_from_function(span, fdecl, true)?
                    }
                    _ => return Ok(None),
                },
                _ => return Ok(None),
            }
        };
        Ok(Some(function))
    }

    /// Make a function that invokes the matching MiniRust intrinsic.
    fn make_intrinsic_function(
        &self,
        span: Span,
        fdecl: &FunDecl,
        intrinsic: mini::IntrinsicOp,
    ) -> Result<mini::Function> {
        let signature = &fdecl.signature;
        let mut builder = FunctionBuilder::new(self, span, signature)?;
        let ret = builder.return_local();
        let arguments: Vec<_> = (0..signature.inputs.len())
            .map(|index| builder.argument(index))
            .collect();
        let start = builder.declare_block();
        let return_block = builder.declare_block();
        builder.set_block(
            start,
            mb::block(
                &[],
                mini::Terminator::Intrinsic {
                    intrinsic,
                    arguments: arguments
                        .iter()
                        .map(|argument| mb::load(mini::PlaceExpr::Local(*argument)))
                        .collect(),
                    ret: mini::PlaceExpr::Local(ret),
                    next_block: Some(return_block),
                },
                mini::BbKind::Regular,
            ),
        );
        builder.set_block(
            return_block,
            mb::block(&[], mini::Terminator::Return, mini::BbKind::Regular),
        );
        Ok(builder.finish())
    }

    /// Implement `core::intrinsics::catch_unwind` in MiniRust.
    fn make_catch_unwind_function(&self, span: Span, fdecl: &FunDecl) -> Result<mini::Function> {
        let signature = &fdecl.signature;
        check!(
            span,
            signature.inputs.len() == 3
                && matches!(signature.inputs[0].kind(), TyKind::FnPtr(_))
                && matches!(signature.inputs[1].kind(), TyKind::RawPtr(..))
                && matches!(signature.inputs[2].kind(), TyKind::FnPtr(_))
                && signature.output.is_bool(),
            "unexpected signature for `core::intrinsics::catch_unwind`"
        );

        let mut builder = FunctionBuilder::new(self, span, signature)?;
        let ret = builder.return_local();
        let try_fn = builder.argument(0);
        let data = builder.argument(1);
        let catch_fn = builder.argument(2);
        let call_ret = builder.add_local(mini::unit_ty());
        let payload_ty = mini::Type::Ptr(mini::PtrType::Raw {
            meta_kind: mini::PointerMetaKind::None,
        });
        let payload = builder.add_local(payload_ty);

        let start = builder.declare_block();
        let returned = builder.declare_block();
        let get_payload = builder.declare_block();
        let call_catch = builder.declare_block();
        let stop_unwind = builder.declare_block();
        let caught = builder.declare_block();
        let load = |local| mb::load(mini::PlaceExpr::Local(local));
        builder.set_block(
            start,
            mb::block(
                &[
                    mini::Statement::StorageLive(call_ret),
                    mini::Statement::StorageLive(payload),
                ],
                mini::Terminator::Call {
                    callee: load(try_fn),
                    calling_convention: mini::CallingConvention::Rust,
                    arguments: [mini::ArgumentExpr::ByValue(load(data))]
                        .into_iter()
                        .collect(),
                    ret: mini::PlaceExpr::Local(call_ret),
                    next_block: Some(returned),
                    unwind_block: Some(get_payload),
                },
                mini::BbKind::Regular,
            ),
        );
        builder.set_block(
            returned,
            mb::block(
                &[mb::assign(
                    mini::PlaceExpr::Local(ret),
                    mb::const_bool(false),
                )],
                mini::Terminator::Return,
                mini::BbKind::Regular,
            ),
        );
        builder.set_block(
            get_payload,
            mb::block(
                &[],
                mini::Terminator::Intrinsic {
                    intrinsic: mini::IntrinsicOp::GetUnwindPayload,
                    arguments: Default::default(),
                    ret: mini::PlaceExpr::Local(payload),
                    next_block: Some(call_catch),
                },
                mini::BbKind::Catch,
            ),
        );
        builder.set_block(
            call_catch,
            mb::block(
                &[],
                mini::Terminator::Call {
                    callee: load(catch_fn),
                    calling_convention: mini::CallingConvention::Rust,
                    arguments: [
                        mini::ArgumentExpr::ByValue(load(data)),
                        mini::ArgumentExpr::ByValue(load(payload)),
                    ]
                    .into_iter()
                    .collect(),
                    ret: mini::PlaceExpr::Local(call_ret),
                    next_block: Some(stop_unwind),
                    // The intrinsic contract requires this function not to unwind.
                    unwind_block: None,
                },
                mini::BbKind::Catch,
            ),
        );
        builder.set_block(
            stop_unwind,
            mb::block(
                &[],
                mini::Terminator::StopUnwind(caught),
                mini::BbKind::Catch,
            ),
        );
        builder.set_block(
            caught,
            mb::block(
                &[mb::assign(
                    mini::PlaceExpr::Local(ret),
                    mb::const_bool(true),
                )],
                mini::Terminator::Return,
                mini::BbKind::Regular,
            ),
        );
        Ok(builder.finish())
    }

    /// Function that starts unwinding.
    fn make_unwind_function(
        &self,
        span: Span,
        fdecl: &FunDecl,
        source: UnwindSource,
    ) -> Result<mini::Function> {
        let mut builder = FunctionBuilder::new(self, span, &fdecl.signature)?;
        let arg = builder.argument(0);
        let start = builder.declare_block();
        let unwind = builder.declare_block();
        builder.set_block(
            start,
            mb::block(
                &[],
                mini::Terminator::StartUnwind {
                    unwind_payload: match source {
                        UnwindSource::ExplicitPayload => mb::load(mini::PlaceExpr::Local(arg)),
                        UnwindSource::OpaquePayload => self.opaque_panic_payload(),
                    },
                    unwind_block: unwind,
                },
                mini::BbKind::Regular,
            ),
        );
        builder.set_block(
            unwind,
            mb::block(&[], mini::Terminator::ResumeUnwind, mini::BbKind::Cleanup),
        );
        Ok(builder.finish())
    }

    /// Compute a DST's layout from the metadata carried by its pointer.
    fn make_layout_of_val_function(
        &self,
        span: Span,
        fdecl: &FunDecl,
        alignment: bool,
    ) -> Result<mini::Function> {
        let signature = &fdecl.signature;
        let [input] = signature.inputs.as_slice() else {
            raise!(span, "unexpected signature for layout-of-value intrinsic")
        };
        let pointee = self.ty(span, input.builtin_deref(self.krate).unwrap())?;

        let mut builder = FunctionBuilder::new(self, span, signature)?;
        let ret = mini::PlaceExpr::Local(builder.return_local());
        let arg = mini::PlaceExpr::Local(builder.argument(0));
        let start = builder.declare_block();
        let metadata = mb::get_metadata(mb::load(arg));
        let value = if alignment {
            mb::compute_align(pointee, metadata)
        } else {
            mb::compute_size(pointee, metadata)
        };
        builder.set_block(
            start,
            mb::block(
                &[mb::assign(ret, value)],
                mini::Terminator::Return,
                mini::BbKind::Regular,
            ),
        );
        Ok(builder.finish())
    }

    /// `cold_path` is only an optimization hint.
    fn make_cold_path_function(&self, span: Span, fdecl: &FunDecl) -> Result<mini::Function> {
        let signature = &fdecl.signature;
        let mut builder = FunctionBuilder::new(self, span, signature)?;
        let ret = mini::PlaceExpr::Local(builder.return_local());
        let start = builder.declare_block();
        builder.set_block(
            start,
            mb::block(
                &[mb::assign(ret, mb::unit())],
                mini::Terminator::Return,
                mini::BbKind::Regular,
            ),
        );
        Ok(builder.finish())
    }

    /// `arith_offset` wraps pointer arithmetic, unlike an in-bounds pointer offset.
    fn make_arith_offset_function(&self, span: Span, fdecl: &FunDecl) -> Result<mini::Function> {
        let signature = &fdecl.signature;
        let [pointer, offset] = signature.inputs.as_slice() else {
            raise!(span, "unexpected signature for `arith_offset`");
        };
        let pointee = pointer
            .builtin_deref(self.krate)
            .ok_or("expected a pointer")
            .context(span)?;
        let (size, _) = self.size_and_align(span, pointee)?;

        let mut builder = FunctionBuilder::new(self, span, signature)?;
        let ret = mini::PlaceExpr::Local(builder.return_local());
        let pointer = mb::load(mini::PlaceExpr::Local(builder.argument(0)));
        let offset_value = mb::load(mini::PlaceExpr::Local(builder.argument(1)));
        let size = mini::ValueExpr::Constant(
            mini::Constant::Int(mini::Int::from(size)),
            self.ty(span, offset)?,
        );
        let value = mb::ptr_offset(
            pointer,
            mb::mul_unchecked(offset_value, size),
            mb::InBounds::No,
        );
        let start = builder.declare_block();
        builder.set_block(
            start,
            mb::block(
                &[mb::assign(ret, value)],
                mini::Terminator::Return,
                mini::BbKind::Regular,
            ),
        );
        Ok(builder.finish())
    }

    /// Compute a pointer distance in elements, checking divisibility and optional nonnegativity.
    fn make_ptr_offset_from_function(
        &self,
        span: Span,
        fdecl: &FunDecl,
        unsigned: bool,
    ) -> Result<mini::Function> {
        let signature = &fdecl.signature;
        let [pointer, _base] = signature.inputs.as_slice() else {
            raise!(span, "unexpected signature for pointer distance intrinsic");
        };
        let pointee = pointer
            .builtin_deref(self.krate)
            .ok_or("expected a pointer")
            .context(span)?;
        let (size, _) = self.size_and_align(span, pointee)?;

        let mut builder = FunctionBuilder::new(self, span, signature)?;
        let ret = mini::PlaceExpr::Local(builder.return_local());
        let pointer = mb::load(mini::PlaceExpr::Local(builder.argument(0)));
        let base = mb::load(mini::PlaceExpr::Local(builder.argument(1)));
        let distance = if unsigned {
            mb::ptr_offset_from_nonneg(pointer, base, mb::InBounds::No)
        } else {
            mb::ptr_offset_from(pointer, base, mb::InBounds::No)
        };
        let distance = mb::div_exact(
            distance,
            mb::const_int_typed::<isize>(mini::Int::from(size)),
        );
        let value = if unsigned {
            mb::int_cast::<usize>(distance)
        } else {
            distance
        };
        let start = builder.declare_block();
        builder.set_block(
            start,
            mb::block(
                &[mb::assign(ret, value)],
                mini::Terminator::Return,
                mini::BbKind::Regular,
            ),
        );
        Ok(builder.finish())
    }
}
