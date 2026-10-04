//! Translate a monomorphized ULLBC crate into MiniRust program.
//!
//! Unsupported features (we translate this incorrectly):
//! - Pointers to statics that aren't at offset 0;
//! - `#[track_caller]`;
//!
//! Unsupported features (will raise an error):
//! - `dyn Trait`;
//! - `CoerceUnsized` pointers;
//! - Unions, because of precise union padding;
use itertools::Itertools;
use minirust_rs::{mem::TreeBorrowsMemory, prelude::TerminationInfo};
use miniutil::build as mb;
use smallvec::{SmallVec, smallvec};
use std::{cell::RefCell, io::Write, marker::PhantomData};

use crate::{
    ast::{from_rustc::LangItem, *},
    errors::{Error, ErrorContext},
    formatter::{FmtCtx, IntoFormatter},
    ids::Generator,
    pretty::FmtWithCtx,
    ullbc_ast::{BlockId, START_BLOCK_ID},
};
use intrinsics::FunctionBuilder;

mod mini {
    pub use minirust_rs::lang::*;
    pub use minirust_rs::libspecr::hidden::GcCow;
    pub use minirust_rs::libspecr::prelude::*;
    pub use minirust_rs::libspecr::{Align, Int, Map, Name, Size};
    pub use minirust_rs::mem::*;
    pub use minirust_rs::prelude::{Target, x86_64};
}

type Result<T> = std::result::Result<T, Error>;

macro_rules! raise {
    ($span:expr, $($fmt:tt)*) => {
        return Err(Error::new($span, format!($($fmt)*)))
    };
}

macro_rules! check {
    ($span:expr, $condition:expr, $($fmt:tt)*) => {
        if !$condition {
            raise!($span, $($fmt)*);
        }
    };
}

mod intrinsics;
mod types;

fn name(index: u32) -> mini::Name {
    mini::Name::from_internal(index)
}

fn mini_size(bytes: u64) -> mini::Size {
    mini::Size::from_bytes_const(bytes)
}

fn mini_align(span: Span, bytes: u64) -> Result<mini::Align> {
    mini::Align::from_bytes(bytes)
        .ok_or("invalid MiniRust alignment")
        .context(span)
}

fn mini_int(value: IntegerValue) -> mini::Int {
    match value {
        IntegerValue::Unsigned(_, value) => mini::Int::from(value),
        IntegerValue::Signed(_, value) => mini::Int::from(value),
    }
}

fn size_bytes(span: Span, size: mini::Size) -> Result<u64> {
    let bytes = size
        .bytes()
        .try_to_usize()
        .ok_or("MiniRust size does not fit usize")
        .context(span)?;
    u64::try_from(bytes)
        .map_err(|_| "MiniRust size does not fit u64")
        .context(span)
}

fn align_bytes(span: Span, align: mini::Align) -> Result<u64> {
    let bytes = align
        .bytes()
        .try_to_usize()
        .ok_or("MiniRust alignment does not fit usize")
        .context(span)?;
    u64::try_from(bytes)
        .map_err(|_| "MiniRust alignment does not fit u64")
        .context(span)
}

pub fn serialize(krate: &TranslatedCrate, writer: impl Write) -> Result<()> {
    let program = TranslateCtx::<mini::x86_64>::new(krate)?.translate()?;
    serde_json::to_writer_pretty(writer, &program)
        .map_err(|error| format!("serializing MiniRust program: {error}"))
        .context(Span::dummy())
}

struct TranslateCtx<'a, T: mini::Target> {
    krate: &'a TranslatedCrate,
    fmt: FmtCtx<'a>,
    target_name: &'a TargetTriple,
    target: &'a TargetInfo,
    global_ids: RefCell<Generator<GlobalDeclId>>,
    string_literals: RefCell<SeqHashMap<String, mini::GlobalName>>,
    mini_target: PhantomData<T>,
}

impl<'a, T: mini::Target> TranslateCtx<'a, T> {
    fn new(krate: &'a TranslatedCrate) -> Result<Self> {
        let (target_name, target) = krate
            .target_information
            .iter()
            .exactly_one()
            .map_err(|_| "MiniRust requires exactly one compilation target")
            .context(Span::dummy())?;
        check!(
            Span::dummy(),
            target.target_pointer_size == size_bytes(Span::dummy(), T::PTR_SIZE)?
                && target.is_little_endian == (T::ENDIANNESS == mini::LittleEndian),
            "the Charon and MiniRust targets do not match"
        );
        Ok(Self {
            krate,
            fmt: krate.into_fmt(),
            target_name,
            target,
            global_ids: RefCell::new(Generator::new_with_init_value(krate.global_decls.next_id())),
            string_literals: RefCell::new(Default::default()),
            mini_target: PhantomData,
        })
    }

    fn fn_name(&self, id: FunDeclId) -> mini::FnName {
        mini::FnName(name(id.index() as u32))
    }

    fn global_name(&self, id: GlobalDeclId) -> mini::GlobalName {
        mini::GlobalName(name(id.index() as u32))
    }

    fn local_name(&self, local: LocalId) -> mini::LocalName {
        mini::LocalName(name(local.index() as u32))
    }

    fn field_name(&self, field: FieldId) -> mini::Int {
        mini::Int::from(field.index() as u128)
    }

    fn block_name(&self, id: BlockId) -> mini::BbName {
        mini::BbName(name(id.index() as u32))
    }

    fn translate(&self) -> Result<mini::Program> {
        let mut functions: mini::Map<mini::FnName, mini::Function> = Default::default();
        for (id, fdecl) in self.krate.fun_decls.iter_enumerated() {
            let span = fdecl.item_meta.span;
            let mini_function = if let Some(function) = self.lower_intrinsic(fdecl)? {
                function
            } else if let Body::Unstructured(body) = &fdecl.body {
                self.function(span, fdecl, body)?
            } else {
                raise!(
                    span,
                    "unable to translate {} to MiniRust",
                    fdecl.def_id.with_ctx(&self.fmt)
                )
            };
            functions.insert(self.fn_name(id), mini_function);
        }

        let mut globals: mini::Map<mini::GlobalName, mini::Global> = Default::default();
        for (id, gdecl) in self.krate.global_decls.iter_enumerated() {
            if matches!(
                gdecl.global_kind,
                GlobalKind::Static {
                    is_thread_local: false,
                    ..
                } | GlobalKind::AnonConst
            ) {
                let mini_global = self.global(gdecl.item_meta.span, gdecl)?;
                globals.insert(self.global_name(id), mini_global);
            }
        }
        for (value, name) in self.string_literals.borrow().iter() {
            globals.insert(
                *name,
                mini::Global {
                    bytes: value.as_bytes().iter().copied().map(Some).collect(),
                    relocations: Default::default(),
                    align: mini::Align::ONE,
                },
            );
        }

        let main = self
            .krate
            .fun_decls
            .iter_enumerated()
            .find(|(_, fdecl)| {
                fdecl
                    .item_meta
                    .name
                    .equals_ref_name(&[&self.krate.crate_name, "main"])
            })
            .map(|(id, _)| id)
            .ok_or("MiniRust needs a `main()` function")
            .context(Span::dummy())?;
        let main_span = self.krate.fun_decls[main].item_meta.span;
        let start = self.fn_name(self.krate.fun_decls.next_id());
        functions.insert(start, self.make_start_function(main_span, main)?);

        Ok(mini::Program {
            functions,
            start,
            globals,
            // FIXME(minirust): translate vtables
            traits: Default::default(),
            vtables: Default::default(),
        })
    }
}

/// Function bodies.
impl<T: mini::Target> TranslateCtx<'_, T> {
    /// Make a start function with the right calling convention that just calls into `main()`.
    fn make_start_function(&self, span: Span, main: FunDeclId) -> Result<mini::Function> {
        let mut signature = self.krate.fun_decls[main].signature.clone();
        signature.abi = Abi::C;
        check!(
            span,
            signature.inputs.is_empty() && signature.output.is_unit(),
            "MiniRust output only supports an entry point with signature `fn main()`"
        );
        let mut builder = FunctionBuilder::new(self, span, &signature)?;
        let ret = builder.return_local();
        let start = builder.declare_block();
        let exit = builder.declare_block();
        let abort = builder.declare_block();
        builder.set_block(
            start,
            mb::block(
                &[],
                mini::Terminator::Call {
                    callee: self.fn_pointer(main),
                    calling_convention: mini::CallingConvention::Rust,
                    arguments: Default::default(),
                    ret: mini::PlaceExpr::Local(ret),
                    next_block: Some(exit),
                    unwind_block: Some(abort),
                },
                mini::BbKind::Regular,
            ),
        );
        builder.set_block(
            exit,
            mb::block(
                &[],
                mini::Terminator::Intrinsic {
                    intrinsic: mini::IntrinsicOp::Exit,
                    arguments: Default::default(),
                    ret: mini::PlaceExpr::Local(ret),
                    next_block: None,
                },
                mini::BbKind::Regular,
            ),
        );
        builder.set_block(
            abort,
            mb::block(
                &[],
                mini::Terminator::Intrinsic {
                    intrinsic: mini::IntrinsicOp::Abort,
                    arguments: Default::default(),
                    ret: mini::PlaceExpr::Local(ret),
                    next_block: None,
                },
                mini::BbKind::Catch,
            ),
        );
        Ok(builder.finish())
    }

    fn function(
        &self,
        span: Span,
        fdecl: &FunDecl,
        body: &ullbc_ast::ExprBody,
    ) -> Result<mini::Function> {
        let locals: mini::Map<mini::LocalName, mini::Type> = body
            .locals
            .iter()
            .map(|local| {
                Ok((
                    self.local_name(local.index),
                    self.ty(local.span, &local.ty)?,
                ))
            })
            .collect::<Result<_>>()?;
        let args: mini::List<mini::LocalName> = body
            .locals
            .arguments()
            .map(|local| self.local_name(local.index))
            .collect();

        let mut blocks = mini::Map::new();
        let mut block_id_gen = Generator::new_with_init_value(body.body.next_idx());
        for (id, block) in body.body.iter_enumerated() {
            let mut current_block = self.block_name(id);
            let mut statements = Vec::new();
            if id == START_BLOCK_ID {
                // Start the function by retagging the function arguments.
                statements.extend(args.iter().map(|arg| mini::Statement::Validate {
                    place: mini::PlaceExpr::Local(arg),
                    fn_entry: true,
                }));
            }
            let block_kind = match block.kind {
                ullbc_ast::UnwindKind::Regular => mini::BbKind::Regular,
                ullbc_ast::UnwindKind::Cleanup => mini::BbKind::Cleanup,
                ullbc_ast::UnwindKind::Terminate => mini::BbKind::Terminate,
            };
            for statement in &block.statements {
                match &statement.kind {
                    // MiniRust keeps the return place and arguments live for the entire call.
                    ullbc_ast::StatementKind::StorageLive(local)
                    | ullbc_ast::StatementKind::StorageDead(local)
                        if body.locals.is_return_or_arg(*local) => {}

                    // These casts are intrinsics for MiniRust.
                    ullbc_ast::StatementKind::Assign(
                        destination,
                        Rvalue::UnaryOp(
                            UnOp::Cast(
                                cast @ (CastKind::PtrExposeProvenance(..)
                                | CastKind::PtrWithExposedProvenance(..)),
                            ),
                            operand,
                        ),
                    ) => {
                        let intrinsic = match cast {
                            CastKind::PtrExposeProvenance(_, target) => {
                                check!(
                                    statement.span,
                                    target.is_usize(),
                                    "MiniRust only supports exposing pointer provenance to `usize`"
                                );
                                mini::IntrinsicOp::PointerExposeProvenance
                            }
                            CastKind::PtrWithExposedProvenance(source, _) => {
                                check!(
                                    statement.span,
                                    source.is_usize(),
                                    "MiniRust only supports creating a pointer from `usize`"
                                );
                                mini::IntrinsicOp::PointerWithExposedProvenance
                            }
                            _ => unreachable!(),
                        };
                        let next_block = self.block_name(block_id_gen.fresh_id());
                        blocks.insert(
                            current_block,
                            mb::block(
                                &std::mem::take(&mut statements),
                                mini::Terminator::Intrinsic {
                                    intrinsic,
                                    arguments: [self.operand(statement.span, operand)?]
                                        .into_iter()
                                        .collect(),
                                    ret: self.place(statement.span, destination)?,
                                    next_block: Some(next_block),
                                },
                                block_kind,
                            ),
                        );
                        current_block = next_block;
                    }

                    _ => statements.extend(self.statement(statement)?),
                }
            }
            let terminator = self.terminator(
                &block.terminator,
                block.kind,
                &mut blocks,
                &mut block_id_gen,
            )?;
            blocks.insert(
                current_block,
                mb::block(&statements, terminator, block_kind),
            );
        }

        Ok(mini::Function {
            locals,
            args,
            ret: self.local_name(body.locals.return_local().index),
            calling_convention: self.calling_convention(span, &fdecl.signature.abi)?,
            blocks,
            start: self.block_name(START_BLOCK_ID),
            implicit_writes: true,
        })
    }

    fn statement(
        &self,
        statement: &ullbc_ast::Statement,
    ) -> Result<SmallVec<[mini::Statement; 1]>> {
        use ullbc_ast::StatementKind as S;
        let span = statement.span;
        Ok(match &statement.kind {
            S::Assign(place, value) => {
                let destination = self.place(span, place)?;
                let mut statements = smallvec![mini::Statement::Assign {
                    destination,
                    source: self.rvalue(span, value)?,
                }];
                if let Rvalue::Use(_, WithRetag::Yes) = value {
                    statements.push(mini::Statement::Validate {
                        place: destination,
                        fn_entry: false,
                    });
                }
                statements
            }
            S::SetDiscriminant(place, variant) => smallvec![mini::Statement::SetDiscriminant {
                destination: self.place(span, place)?,
                value: self.variant_discriminant(span, place.ty(), *variant)?,
            }],
            S::StorageLive(local) => {
                smallvec![mini::Statement::StorageLive(self.local_name(*local))]
            }
            S::StorageDead(local) => {
                smallvec![mini::Statement::StorageDead(self.local_name(*local))]
            }
            S::PlaceMention(place) => {
                smallvec![mini::Statement::PlaceMention(self.place(span, place)?)]
            }
            S::Borrowck(_) | S::Nop => SmallVec::new(),
            S::Assert { .. } => {
                raise!(
                    span,
                    "MiniRust is incompatible with `--reconstruct-asserts`"
                )
            }
        })
    }

    fn terminator(
        &self,
        terminator: &ullbc_ast::Terminator,
        unwind_kind: ullbc_ast::UnwindKind,
        extra_blocks: &mut mini::Map<mini::BbName, mini::BasicBlock>,
        block_id_gen: &mut Generator<BlockId>,
    ) -> Result<mini::Terminator> {
        use ullbc_ast::TerminatorKind as T;
        let span = terminator.span;
        Ok(match &terminator.kind {
            T::Goto { target } => mini::Terminator::Goto(self.block_name(*target)),
            T::Switch { data, branches } => {
                let value = self.switch_value(span, &data.scrutinee)?;
                let cases = data
                    .branches
                    .iter()
                    .map(|(value, branch)| -> Result<_> {
                        Ok((
                            self.constant_int(span, value)?,
                            self.block_name(branches[*branch]),
                        ))
                    })
                    .try_collect()?;
                let fallback = if let Some(branch) = data.fallback {
                    self.block_name(branches[branch])
                } else {
                    let name = self.block_name(block_id_gen.fresh_id());
                    extra_blocks.insert(
                        name,
                        mb::block(&[], mini::Terminator::Unreachable, mini::BbKind::Regular),
                    );
                    name
                };
                mini::Terminator::Switch {
                    value,
                    cases,
                    fallback,
                }
            }
            T::Call {
                call,
                target,
                on_unwind,
            } => mini::Terminator::Call {
                callee: match &call.func {
                    FnOperand::Regular(fn_ptr) => match *fn_ptr.kind {
                        FnPtrKind::Fun(id) => self.fn_pointer(id),
                        FnPtrKind::Trait(..) => {
                            raise!(span, "trait-method call remained after monomorphization")
                        }
                    },
                    FnOperand::Dynamic(operand) => self.operand(span, operand)?,
                },
                calling_convention: self.callee_convention(span, &call.func)?,
                arguments: call
                    .args
                    .iter()
                    .map(|arg| {
                        Ok(match arg {
                            Operand::Move(place) => {
                                mini::ArgumentExpr::InPlace(self.place(span, place)?)
                            }
                            _ => mini::ArgumentExpr::ByValue(self.operand(span, arg)?),
                        })
                    })
                    .collect::<Result<_>>()?,
                ret: self.place(span, &call.dest)?,
                next_block: Some(self.block_name(*target)),
                unwind_block: Some(self.block_name(*on_unwind)),
            },
            T::Assert {
                assert,
                target,
                on_unwind,
            } => {
                let condition = mb::bool_to_int::<u8>(self.operand(span, &assert.cond)?);
                let success = self.block_name(*target);
                let failure = if unwind_kind != ullbc_ast::UnwindKind::Regular {
                    // A second panic while unwinding follows the pre-existing terminate path.
                    self.block_name(*on_unwind)
                } else {
                    let name = self.block_name(block_id_gen.fresh_id());
                    extra_blocks.insert(
                        name,
                        mb::block(&[], self.start_unwind(*on_unwind), mini::BbKind::Regular),
                    );
                    name
                };
                let (cases, fallback) = if assert.expected {
                    ([(mini::Int::from(1), success)], failure)
                } else {
                    ([(mini::Int::from(0), success)], failure)
                };
                mini::Terminator::Switch {
                    value: condition,
                    cases: cases.into_iter().collect(),
                    fallback,
                }
            }
            T::UndefinedBehavior => mini::Terminator::Unreachable,
            T::UnwindTerminate => mini::Terminator::Intrinsic {
                intrinsic: mini::IntrinsicOp::Abort,
                arguments: Default::default(),
                ret: mini::PlaceExpr::Local(self.local_name(LocalId::ZERO)),
                next_block: None,
            },
            T::Return => mini::Terminator::Return,
            T::UnwindResume => mini::Terminator::ResumeUnwind,
            T::Drop { .. } => raise!(span, "MiniRust requires drops to be desugared"),
            T::InlineAsm { .. } => raise!(span, "MiniRust does not support inline assembly"),
            T::Panic { .. } => raise!(
                span,
                "MiniRust output does not support --reconstruct-panic-calls"
            ),
        })
    }

    fn start_unwind(&self, on_unwind: BlockId) -> mini::Terminator {
        mini::Terminator::StartUnwind {
            unwind_payload: self.opaque_panic_payload(),
            unwind_block: self.block_name(on_unwind),
        }
    }

    fn opaque_panic_payload(&self) -> mini::ValueExpr {
        // FIXME(minirust): preserve Rust's actual panic payload. For now we use a dangling
        // pointer, as MiniRust only models an opaque raw-pointer payload.
        mini::ValueExpr::Constant(
            mini::Constant::PointerWithoutProvenance(mini::Int::from(1)),
            mini::Type::Ptr(mini::PtrType::Raw {
                meta_kind: mini::PointerMetaKind::None,
            }),
        )
    }

    fn place(&self, span: Span, place: &Place) -> Result<mini::PlaceExpr> {
        Ok(match &place.kind {
            PlaceKind::Local(local) => mini::PlaceExpr::Local(self.local_name(*local)),
            PlaceKind::Global(gref) => {
                let pointer = mini::ValueExpr::Constant(
                    mini::Constant::GlobalPointer(mini::Relocation {
                        name: self.global_name(gref.id),
                        offset: mini_size(0),
                    }),
                    mini::Type::Ptr(mini::PtrType::Raw {
                        meta_kind: mini::PointerMetaKind::None,
                    }),
                );
                let meta_kind = self.metadata_kind(span, &place.ty)?;
                let pointer = if meta_kind == mini::PointerMetaKind::None {
                    pointer
                } else {
                    let metadata = &self.krate.global_decls[gref.id].ptr_metadata;
                    mb::construct_wide_pointer(
                        pointer,
                        self.constant(span, metadata)?,
                        mb::raw_ptr_ty(meta_kind),
                    )
                };
                mb::deref(pointer, self.ty(span, &place.ty)?)
            }
            PlaceKind::Projection(subplace, projection) => {
                let subplace_expr = self.place(span, subplace)?;
                match projection {
                    ProjectionElem::Deref => {
                        mb::deref(mb::load(subplace_expr), self.ty(span, &place.ty)?)
                    }
                    ProjectionElem::Field(variant, field) => {
                        let subplace_expr = if let Some(variant) = variant {
                            mb::downcast(
                                subplace_expr,
                                self.variant_discriminant(span, subplace.ty(), *variant)?,
                            )
                        } else {
                            subplace_expr
                        };
                        mb::field(subplace_expr, self.field_name(*field))
                    }
                    ProjectionElem::Index {
                        offset,
                        from_end: false,
                    } => mb::index(subplace_expr, self.operand(span, offset)?),
                    ProjectionElem::Index { from_end: true, .. }
                    | ProjectionElem::Subslice { .. }
                    | ProjectionElem::PtrMetadata => {
                        raise!(
                            span,
                            "Failed to translate place to MiniRust: {}",
                            place.with_ctx(&self.fmt)
                        )
                    }
                }
            }
        })
    }

    fn operand(&self, span: Span, operand: &Operand) -> Result<mini::ValueExpr> {
        Ok(match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if let PlaceKind::Projection(pointer, ProjectionElem::PtrMetadata) = &place.kind {
                    mb::get_metadata(mb::load(self.place(span, pointer)?))
                } else {
                    mb::load(self.place(span, place)?)
                }
            }
            Operand::Const(value) => self.constant(span, value)?,
        })
    }

    fn switch_value(&self, span: Span, scrutinee: &SwitchScrutinee) -> Result<mini::ValueExpr> {
        let (value, ty) = match scrutinee {
            SwitchScrutinee::Value(operand) => (self.operand(span, operand)?, operand.ty()),
            SwitchScrutinee::Discriminant(place) => {
                (mb::get_discriminant(self.place(span, place)?), place.ty())
            }
        };
        if matches!(ty.kind(), TyKind::Scalar(ScalarTy::Bool)) {
            Ok(mb::bool_to_int::<u8>(value))
        } else {
            Ok(value)
        }
    }

    fn rvalue(&self, span: Span, value: &Rvalue) -> Result<mini::ValueExpr> {
        Ok(match value {
            // Retagging is handled at the statement level.
            Rvalue::Use(operand, _) => self.operand(span, operand)?,
            Rvalue::Ref { place, kind, .. } => mini::ValueExpr::AddrOf {
                target: mini::GcCow::new(self.place(span, place)?),
                ptr_ty: mini::PtrType::Ref {
                    mutbl: if kind.is_mut() {
                        mini::Mutability::Mutable
                    } else {
                        mini::Mutability::Immutable
                    },
                    pointee: self.pointee_info(span, place.ty())?,
                },
            },
            Rvalue::RawPtr { place, .. } => mini::ValueExpr::AddrOf {
                target: mini::GcCow::new(self.place(span, place)?),
                ptr_ty: mini::PtrType::Raw {
                    meta_kind: self.metadata_kind(span, place.ty())?,
                },
            },
            Rvalue::BinaryOp(op, left, right) => self.binop(span, *op, left, right)?,
            Rvalue::UnaryOp(op, operand) => self.unop(span, op, operand)?,
            Rvalue::NullaryOp(op) => {
                let checks = self.krate.runtime_checks;
                let value = match op {
                    NullOp::UbChecks => checks.ub_checks,
                    NullOp::OverflowChecks => checks.overflow_checks,
                    NullOp::ContractChecks => checks.contract_checks,
                };
                mb::const_bool(value)
            }
            Rvalue::Discriminant(place) => mb::get_discriminant(self.place(span, place)?),
            Rvalue::Aggregate(kind, operands) => self.aggregate(span, kind, operands)?,
            Rvalue::Len(place, _, known_len) => {
                if let Some(len) = known_len {
                    self.constant(span, len)?
                } else {
                    let ptr = mini::ValueExpr::AddrOf {
                        target: mini::GcCow::new(self.place(span, place)?),
                        ptr_ty: mini::PtrType::Raw {
                            meta_kind: mini::PointerMetaKind::ElementCount,
                        },
                    };
                    mb::get_metadata(ptr)
                }
            }
            Rvalue::Repeat(operand, ty, count, _) => {
                let count = count
                    .as_usize_literal()
                    .ok_or("non-concrete array length")
                    .context(span)?;
                let count = usize::try_from(count)
                    .map_err(|_| "array length does not fit usize")
                    .context(span)?;
                let value = self.operand(span, operand)?;
                mb::array(&vec![value; count], self.ty(span, ty)?)
            }
        })
    }

    fn binop(
        &self,
        span: Span,
        op: BinOp,
        left: &Operand,
        right: &Operand,
    ) -> Result<mini::ValueExpr> {
        let left_value = self.operand(span, left)?;
        let mut right_value = self.operand(span, right)?;

        let overflowing_op = |mode, regular, unchecked| {
            Ok(match mode {
                OverflowMode::Wrap => regular,
                OverflowMode::UB => unchecked,
                OverflowMode::Panic => raise!(
                    span,
                    "MiniRust translation is incompatible with `--reconstruct-fallible-operations`"
                ),
            })
        };
        let operator = match op {
            BinOp::BitXor => mini::BinOp::Int(mini::IntBinOp::BitXor),
            BinOp::BitAnd => mini::BinOp::Int(mini::IntBinOp::BitAnd),
            BinOp::BitOr => mini::BinOp::Int(mini::IntBinOp::BitOr),
            BinOp::Eq => mini::BinOp::Rel(mini::RelOp::Eq),
            BinOp::Lt => mini::BinOp::Rel(mini::RelOp::Lt),
            BinOp::Le => mini::BinOp::Rel(mini::RelOp::Le),
            BinOp::Ne => mini::BinOp::Rel(mini::RelOp::Ne),
            BinOp::Ge => mini::BinOp::Rel(mini::RelOp::Ge),
            BinOp::Gt => mini::BinOp::Rel(mini::RelOp::Gt),
            BinOp::AddChecked => mini::BinOp::IntWithOverflow(mini::IntBinOpWithOverflow::Add),
            BinOp::SubChecked => mini::BinOp::IntWithOverflow(mini::IntBinOpWithOverflow::Sub),
            BinOp::MulChecked => mini::BinOp::IntWithOverflow(mini::IntBinOpWithOverflow::Mul),
            BinOp::Add(mode) => mini::BinOp::Int(overflowing_op(
                mode,
                mini::IntBinOp::Add,
                mini::IntBinOp::AddUnchecked,
            )?),
            BinOp::Sub(mode) => mini::BinOp::Int(overflowing_op(
                mode,
                mini::IntBinOp::Sub,
                mini::IntBinOp::SubUnchecked,
            )?),
            BinOp::Mul(mode) => mini::BinOp::Int(overflowing_op(
                mode,
                mini::IntBinOp::Mul,
                mini::IntBinOp::MulUnchecked,
            )?),
            BinOp::Div(_) => mini::BinOp::Int(mini::IntBinOp::Div),
            BinOp::Rem(_) => mini::BinOp::Int(mini::IntBinOp::Rem),
            BinOp::Shl(mode) => mini::BinOp::Int(overflowing_op(
                mode,
                mini::IntBinOp::Shl,
                mini::IntBinOp::ShlUnchecked,
            )?),
            BinOp::Shr(mode) => mini::BinOp::Int(overflowing_op(
                mode,
                mini::IntBinOp::Shr,
                mini::IntBinOp::ShrUnchecked,
            )?),
            BinOp::Cmp => mini::BinOp::Rel(mini::RelOp::Cmp),
            BinOp::Offset => {
                let pointee = left
                    .ty()
                    .builtin_deref(self.krate)
                    .ok_or("pointer offset on a non-pointer")
                    .context(span)?;
                let (size, _) = self.size_and_align(span, pointee)?;
                let size = mini::ValueExpr::Constant(
                    mini::Constant::Int(mini::Int::from(size)),
                    self.ty(span, right.ty())?,
                );
                right_value = mini::ValueExpr::BinOp {
                    operator: mini::BinOp::Int(mini::IntBinOp::MulUnchecked),
                    left: mini::GcCow::new(right_value),
                    right: mini::GcCow::new(size),
                };
                mini::BinOp::PtrOffset { inbounds: true }
            }
        };

        if left.ty().is_bool() && matches!(operator, mini::BinOp::Int(_)) {
            let value = mini::ValueExpr::BinOp {
                operator,
                left: mini::GcCow::new(mb::bool_to_int::<u8>(left_value)),
                right: mini::GcCow::new(mb::bool_to_int::<u8>(right_value)),
            };
            Ok(mb::transmute(value, mini::Type::Bool))
        } else {
            Ok(mini::ValueExpr::BinOp {
                operator,
                left: mini::GcCow::new(left_value),
                right: mini::GcCow::new(right_value),
            })
        }
    }

    fn unop(&self, span: Span, op: &UnOp, operand: &Operand) -> Result<mini::ValueExpr> {
        let mut operand_value = self.operand(span, operand)?;
        let operator = match op {
            UnOp::Not if operand.ty().is_bool() => {
                return Ok(mb::not(operand_value));
            }
            UnOp::Not => mini::UnOp::Int(mini::IntUnOp::BitNot),
            UnOp::Neg(_) => mini::UnOp::Int(mini::IntUnOp::Neg),
            UnOp::Cast(CastKind::Scalar(source_ty, target_ty)) => {
                if matches!(source_ty, ScalarTy::Bool) {
                    operand_value = mb::bool_to_int::<u8>(operand_value);
                }
                mini::UnOp::Cast(mini::CastOp::IntToInt(match *target_ty {
                    ScalarTy::Integer(ty) => self.int_type(ty),
                    ScalarTy::Char => self.int_type(IntegerTy::Unsigned(UIntTy::U32)),
                    ScalarTy::Bool => self.int_type(IntegerTy::Unsigned(UIntTy::U8)),
                    ScalarTy::Float(_) => raise!(span, "float unexpected in a scalar cast"),
                }))
            }
            UnOp::Cast(CastKind::Transmute(_, target_ty)) => {
                mini::UnOp::Cast(mini::CastOp::Transmute(self.ty(span, target_ty)?))
            }
            UnOp::Cast(CastKind::RawPtr(source_ty, target_ty)) => {
                // MiniRust does not track the type of pointers, so the only effect of this cast is
                // on metadata.
                let old = self.metadata_kind(
                    span,
                    source_ty
                        .builtin_deref(self.krate)
                        .ok_or("raw-pointer cast from a non-pointer")
                        .context(span)?,
                )?;
                let new = self.metadata_kind(
                    span,
                    target_ty
                        .builtin_deref(self.krate)
                        .ok_or("raw-pointer cast to a non-pointer")
                        .context(span)?,
                )?;
                if old == new {
                    return Ok(operand_value);
                }
                if matches!(new, mini::PointerMetaKind::None) {
                    mini::UnOp::GetThinPointer
                } else {
                    raise!(span, "raw-pointer cast adds metadata")
                }
            }
            // Handled at the statement level.
            UnOp::Cast(
                CastKind::PtrExposeProvenance(..) | CastKind::PtrWithExposedProvenance(..),
            ) => unreachable!(),
            UnOp::Cast(CastKind::FnPtr(source_ty, _)) => {
                match source_ty.kind() {
                    // Turn the function-item ZST into a function pointer.
                    TyKind::FnDef(fn_ptr) => {
                        let FnPtrKind::Fun(id) = *fn_ptr.skip_binder.kind else {
                            raise!(span, "method reference remained after monomorphization")
                        };
                        return Ok(self.fn_pointer(id));
                    }
                    // MiniRust function pointer values are untyped.
                    TyKind::FnPtr(..) => return Ok(operand_value),
                    _ => raise!(
                        span,
                        "unexpected type for function pointer cast: {}",
                        source_ty.with_ctx(&self.fmt)
                    ),
                }
            }
            UnOp::Cast(CastKind::Unsize(_, target_ty, UnsizingMetadata::Length(len))) => {
                let target_ty = self.ty(span, target_ty)?;
                let mini::Type::Ptr(_) = target_ty else {
                    raise!(span, "unsizing target is not a pointer")
                };
                return Ok(mb::construct_wide_pointer(
                    operand_value,
                    self.constant(span, len)?,
                    target_ty,
                ));
            }
            // FIXME(minirust): add vtable support
            UnOp::Cast(CastKind::Unsize(..) | CastKind::Concretize(..)) => {
                raise!(span, "MiniRust output does not support `dyn Trait`")
            }
        };
        Ok(mini::ValueExpr::UnOp {
            operator,
            operand: mini::GcCow::new(operand_value),
        })
    }

    fn aggregate(
        &self,
        span: Span,
        kind: &AggregateKind,
        operands: &[Operand],
    ) -> Result<mini::ValueExpr> {
        let values: Vec<_> = operands
            .iter()
            .map(|operand| self.operand(span, operand))
            .try_collect()?;
        Ok(match kind {
            AggregateKind::Adt(tref, variant, union_field) => {
                let ty = self.ty(span, &TyKind::Adt(tref.clone()).into_ty())?;
                if let Some(field) = union_field {
                    mini::ValueExpr::Union {
                        field: self.field_name(*field),
                        expr: mini::GcCow::new(values.into_iter().next().unwrap()),
                        union_ty: ty,
                    }
                } else if let Some(variant) = variant {
                    let discriminant = self.variant_discriminant_for_tref(span, tref, *variant)?;
                    let variant_ty = match &ty {
                        mini::Type::Enum { variants, .. } => variants
                            .iter()
                            .find(|(candidate, _)| *candidate == discriminant)
                            .map(|(_, variant)| variant.ty)
                            .ok_or("missing MiniRust enum variant")
                            .context(span)?,
                        _ => raise!(span, "enum aggregate has non-enum type"),
                    };
                    mb::variant(
                        discriminant,
                        mini::ValueExpr::Tuple(values.into_iter().collect(), variant_ty),
                        ty,
                    )
                } else {
                    mini::ValueExpr::Tuple(values.into_iter().collect(), ty)
                }
            }
            AggregateKind::Array(element, count, _) => {
                let count = count
                    .as_usize_literal()
                    .ok_or("non-concrete array length")
                    .context(span)?;
                mini::ValueExpr::Tuple(
                    values.into_iter().collect(),
                    mini::Type::Array {
                        elem: mini::GcCow::new(self.ty(span, element)?),
                        count: mini::Int::from(count),
                    },
                )
            }
            AggregateKind::RawPtr(pointee, _) => {
                check!(
                    span,
                    values.len() == 2,
                    "raw pointer aggregate does not have two fields"
                );
                let ptr_ty = mini::PtrType::Raw {
                    meta_kind: self.metadata_kind(span, pointee)?,
                };
                mb::construct_wide_pointer(values[0], values[1], mini::Type::Ptr(ptr_ty))
            }
        })
    }

    fn fn_pointer(&self, id: FunDeclId) -> mini::ValueExpr {
        mb::fn_ptr(self.fn_name(id))
    }

    fn calling_convention(&self, span: Span, abi: &Abi) -> Result<mini::CallingConvention> {
        Ok(match abi {
            Abi::Rust => mini::CallingConvention::Rust,
            Abi::C => mini::CallingConvention::C,
            Abi::Other(name) => {
                raise!(
                    span,
                    "calling convention `{name}` is not supported by MiniRust"
                )
            }
        })
    }

    fn callee_convention(
        &self,
        span: Span,
        operand: &FnOperand,
    ) -> Result<mini::CallingConvention> {
        let signature = match operand {
            FnOperand::Regular(fn_ptr) => match *fn_ptr.kind {
                FnPtrKind::Fun(id) => {
                    &self
                        .krate
                        .fun_decls
                        .get(id)
                        .ok_or_else(|| format!("missing function {}", id.with_ctx(&self.fmt)))
                        .context(span)?
                        .signature
                }
                FnPtrKind::Trait(..) => {
                    raise!(span, "trait-method call remained after monomorphization")
                }
            },
            FnOperand::Dynamic(operand) => match operand.ty().kind() {
                TyKind::FnPtr(signature) => &signature.skip_binder,
                _ => raise!(span, "dynamic callee is not a function pointer"),
            },
        };
        self.calling_convention(span, &signature.abi)
    }
}

/// Constants
impl<T: mini::Target> TranslateCtx<'_, T> {
    pub(super) fn global(&self, span: Span, gdecl: &GlobalDecl) -> Result<mini::Global> {
        let ConstantExprKind::RawMemory(memory) = gdecl.value.kind() else {
            raise!(
                span,
                "MiniRust output needs all globals to be evaluated to raw bytes: {}",
                gdecl.value.with_ctx(&self.fmt)
            )
        };
        if gdecl.ty.get_ptr_metadata(self.krate).is_none() {
            check!(
                span,
                u64::try_from(memory.len()).context(span)? == self.size(span, &gdecl.size)?,
                "global value and layout have different sizes"
            );
        }
        let mut bytes = mini::List::new();
        let mut relocations = mini::List::new();
        for (offset, byte) in memory.iter().enumerate() {
            match byte {
                Byte::Uninit => bytes.push(None),
                Byte::Value(value) => bytes.push(Some(*value)),
                Byte::Provenance(provenance, pointer_byte) => {
                    let name = match provenance {
                        Provenance::Global(gref) => self.global_name(gref.id),
                        Provenance::Function(_) => {
                            raise!(span, "MiniRust globals cannot contain function pointers")
                        }
                        Provenance::Unknown => {
                            raise!(span, "global contains a pointer with unknown provenance")
                        }
                    };
                    // FIXME(minirust): MiniRust does not seem to support pointer fragments
                    if *pointer_byte == 0 {
                        relocations.push((
                            mini_size(u64::try_from(offset).context(span)?),
                            mini::Relocation {
                                name,
                                // FIXME(minirust): Charon's raw bytes do not record the offset
                                // within the target allocation.
                                offset: mini::Size::ZERO,
                            },
                        ));
                    }
                    // MiniRust overwrites these bytes when applying the relocation.
                    bytes.push(None);
                }
            }
        }
        Ok(mini::Global {
            bytes,
            relocations,
            align: mini_align(span, self.size(span, &gdecl.align)?)?,
        })
    }

    pub(super) fn constant(&self, span: Span, constant: &ConstantExpr) -> Result<mini::ValueExpr> {
        let ty = self.ty(span, constant.ty())?;
        Ok(match constant.kind() {
            ConstantExprKind::Bool(value) => mb::const_bool(*value),
            ConstantExprKind::Integer(value) => {
                mini::ValueExpr::Constant(mini::Constant::Int(mini_int(*value)), ty)
            }
            // FIXME(minirust): MiniRust does not check the validity of chars.
            ConstantExprKind::Char(_) => raise!(span, "MiniRust does not support the `char` type"),
            ConstantExprKind::Adt(variant, fields) => {
                let values = fields
                    .iter()
                    .map(|field| self.constant(span, field))
                    .try_collect()?;
                if let Some(variant) = variant {
                    let tref = constant
                        .ty()
                        .as_adt()
                        .ok_or("enum constant without ADT type")
                        .context(span)?;
                    let discriminant = self.variant_discriminant_for_tref(span, tref, *variant)?;
                    let variant_ty = match &ty {
                        mini::Type::Enum { variants, .. } => variants
                            .iter()
                            .find(|(candidate, _)| *candidate == discriminant)
                            .map(|(_, variant)| variant.ty)
                            .ok_or("missing enum variant")
                            .context(span)?,
                        _ => raise!(span, "enum constant translated to non-enum type"),
                    };
                    mb::variant(discriminant, mini::ValueExpr::Tuple(values, variant_ty), ty)
                } else {
                    mini::ValueExpr::Tuple(values, ty)
                }
            }
            ConstantExprKind::Array(values) => mini::ValueExpr::Tuple(
                values
                    .iter()
                    .map(|value| self.constant(span, value))
                    .try_collect()?,
                ty,
            ),
            ConstantExprKind::Str(value) => {
                let mut literals = self.string_literals.borrow_mut();
                let name = if let Some(name) = literals.get(value) {
                    *name
                } else {
                    let name = self.global_name(self.global_ids.borrow_mut().fresh_id());
                    literals.insert(value.clone(), name);
                    name
                };
                mb::construct_wide_pointer(
                    mini::ValueExpr::Constant(
                        mini::Constant::GlobalPointer(mini::Relocation {
                            name,
                            offset: mini::Size::ZERO,
                        }),
                        mini::Type::Ptr(mini::PtrType::Raw {
                            meta_kind: mini::PointerMetaKind::None,
                        }),
                    ),
                    mini::ValueExpr::Constant(
                        mini::Constant::Int(mini::Int::from(value.len())),
                        mb::int_ty(mini::Signedness::Unsigned, T::PTR_SIZE),
                    ),
                    ty,
                )
            }
            ConstantExprKind::FnDef(_) => mini::ValueExpr::Tuple(Default::default(), ty),
            ConstantExprKind::FnPtr(fn_ptr) => match *fn_ptr.kind {
                FnPtrKind::Fun(id) => self.fn_pointer(id),
                FnPtrKind::Trait(..) => {
                    raise!(
                        span,
                        "trait function pointer remained after monomorphization"
                    )
                }
            },
            ConstantExprKind::Cast(value, target_ty) => {
                mb::transmute(self.constant(span, value)?, self.ty(span, target_ty)?)
            }
            ConstantExprKind::PtrNoProvenance(value) => mini::ValueExpr::Constant(
                mini::Constant::PointerWithoutProvenance(mini::Int::from(*value)),
                ty,
            ),
            ConstantExprKind::Discriminant(tref, variant) => mini::ValueExpr::Constant(
                mini::Constant::Int(self.variant_discriminant_for_tref(span, tref, *variant)?),
                ty,
            ),
            ConstantExprKind::SizeOf(value) => {
                let (size, _) = self.size_and_align(span, value)?;
                mini::ValueExpr::Constant(mini::Constant::Int(mini::Int::from(size)), ty)
            }
            ConstantExprKind::AlignOf(value) => {
                let (_, align) = self.size_and_align(span, value)?;
                mini::ValueExpr::Constant(mini::Constant::Int(mini::Int::from(align)), ty)
            }
            _ => raise!(
                span,
                "unsupported MiniRust constant: {}",
                constant.with_ctx(&self.fmt)
            ),
        })
    }

    pub(super) fn constant_int(&self, span: Span, constant: &ConstantExpr) -> Result<mini::Int> {
        Ok(match self.constant(span, constant)? {
            mini::ValueExpr::Constant(c, _) => match c {
                mini::Constant::Int(int) => int,
                mini::Constant::Bool(b) => mini::Int::from(u128::from(b)),
                _ => raise!(
                    span,
                    "switch case is not an integer constant: {}",
                    constant.with_ctx(&self.fmt)
                ),
            },
            _ => raise!(
                span,
                "switch case is not an integer constant: {}",
                constant.with_ctx(&self.fmt)
            ),
        })
    }
}

pub enum RunError {
    Translation(Error),
    Panic,
    Ub(String),
    Other(TerminationInfo),
}

pub fn run<T>(krate: &TranslatedCrate) -> std::result::Result<(), RunError>
where
    T: mini::Target + serde::Serialize + serde::de::DeserializeOwned,
{
    let translator = TranslateCtx::<T>::new(krate).map_err(RunError::Translation)?;
    let program = translator.translate().map_err(RunError::Translation)?;
    match miniutil::run::run_program::<TreeBorrowsMemory<T>>(program) {
        TerminationInfo::MachineStop => Ok(()),
        TerminationInfo::IllFormed(message) => Err(RunError::Translation(Error::new(
            Span::dummy(),
            format!("MiniRust rejected the program: {message}"),
        ))),
        TerminationInfo::Abort => Err(RunError::Panic),
        TerminationInfo::Ub(message) => Err(RunError::Ub(message.to_string())),
        error @ (TerminationInfo::Deadlock | TerminationInfo::MemoryLeak) => {
            Err(RunError::Other(error))
        }
    }
}
