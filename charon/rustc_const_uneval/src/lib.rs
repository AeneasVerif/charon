//! Read evaluated constants back into structured values, using rustc's const-eval interpreter.
//! This only depends on rustc: naming the items and allocations we encounter is left to the
//! caller.
#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_attr_ir;
extern crate rustc_const_eval;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

mod eval;
mod memory;
mod valtree;

pub use eval::promoted_body;

use rustc_abi::VariantIdx;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{self, interpret};
use rustc_middle::ty::{self, Ty, TyCtxt};

/// The options that affect how constants are read.
#[derive(Debug, Clone, Copy, Default)]
pub struct Config {
    /// Whether to refer to anonymous allocations (e.g. the bytes of `b"foo"`) as globals, or to
    /// inline their contents at each use.
    pub anon_allocs_as_globals: bool,
}

/// Evaluates and reads constants in a given typing environment.
pub struct ConstReader<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub typing_env: ty::TypingEnv<'tcx>,
    pub config: Config,
}

/// A constant that we can ask rustc to evaluate.
#[derive(Debug, Clone, Copy)]
pub enum ConstSource<'tcx> {
    /// A `const` item or associated const.
    Item {
        def_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
    },
    /// A promoted constant in the body of `def_id`.
    Promoted {
        def_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
        promoted: mir::Promoted,
    },
    /// The contents of a global, viewed at type [`ConstReader::global_ty`].
    Global(GlobalRef),
    /// A type-system constant, e.g. an array length or an inline `const {}` block.
    TyConst(ty::AliasConst<'tcx>),
    /// An already-evaluated type-system constant.
    ValTree(ty::Value<'tcx>),
    /// An already-evaluated constant, e.g. found in MIR.
    Value(mir::ConstValue, Ty<'tcx>),
}

/// How to read back an evaluated constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReadMode {
    /// As a structured value (literals, ADTs, references...).
    Structured,
    /// As raw bytes ([`ConstKind::Memory`]).
    Bytes,
}

/// Why [`ConstReader::read`] failed.
#[derive(Debug)]
pub enum ReadError<'tcx> {
    /// Rustc can't evaluate the constant, e.g. because it is generic, its evaluation failed, or
    /// it is an extern static.
    NotEvaluable,
    /// The const-eval interpreter can't load the evaluated value, e.g. because its type is too
    /// generic to have a layout.
    NotLoadable,
    /// The interpreter failed while reading back the evaluated value.
    Read(interpret::InterpErrorInfo<'tcx>),
}

impl<'tcx> From<interpret::InterpErrorInfo<'tcx>> for ReadError<'tcx> {
    fn from(err: interpret::InterpErrorInfo<'tcx>) -> Self {
        ReadError::Read(err)
    }
}

/// A constant of type `ty`, read back from its evaluated representation.
#[derive(Debug, Clone)]
pub struct Const<'tcx> {
    pub ty: Ty<'tcx>,
    pub kind: ConstKind<'tcx>,
}

/// The value of a constant. A pattern-typed value read from memory keeps its pattern type, and its
/// kind is that of the base type; when read from a valtree it is read at the base type.
#[derive(Debug, Clone)]
pub enum ConstKind<'tcx> {
    /// A boolean, character, integer or float.
    Scalar(ty::ScalarInt),
    /// A pointer without provenance, i.e. a plain address.
    PtrNoProvenance(u128),
    /// A string slice.
    Str(String),
    /// A `str` constant that isn't valid UTF-8.
    ByteStr(Vec<u8>),
    /// A struct, enum, tuple, closure, array or slice. `variant` is set for structs and enums.
    Aggregate {
        variant: Option<VariantIdx>,
        fields: Vec<Const<'tcx>>,
    },
    /// A function item. This is a ZST, unlike `FnPtr`.
    FnDef {
        def: DefId,
        args: ty::GenericArgsRef<'tcx>,
    },
    /// A function pointer.
    FnPtr(ty::Instance<'tcx>),
    /// A valid reference or raw pointer; `ty` tells which.
    Ptr {
        target: PtrTarget<'tcx>,
        /// For a wide pointer, how to recover it from a thin pointer to the target.
        unsize: Option<Unsize<'tcx>>,
    },
    /// The raw bytes of the value. Used for values that have no structured representation (e.g.
    /// unions).
    Memory(Vec<Byte<'tcx>>),
    /// A valid constant that we can't represent.
    Unsupported(&'static str),
}

impl<'tcx> ConstKind<'tcx> {
    /// A `str` constant with the given bytes.
    fn str(bytes: Vec<u8>) -> Self {
        match String::from_utf8(bytes) {
            Ok(str) => ConstKind::Str(str),
            Err(err) => ConstKind::ByteStr(err.into_bytes()),
        }
    }

    /// The value of the function item type `ty`.
    fn fn_def(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Self {
        let ty::FnDef(def, args) = *ty.kind() else {
            unreachable!("expected a function item type, got {ty:?}")
        };
        ConstKind::FnDef {
            def,
            // Note: loss of precision, we erase the bound vars.
            args: rustc_trait_elaboration::erase_free_regions(tcx, args.skip_binder()),
        }
    }
}

/// What a pointer points to.
#[derive(Debug, Clone)]
pub enum PtrTarget<'tcx> {
    /// A global, viewed at type `ty`.
    Global { global: GlobalRef, ty: Ty<'tcx> },
    /// The value behind the pointer, when we don't refer to its global by name.
    Inline(Box<Const<'tcx>>),
}

/// The unsizing that turns a thin pointer to the target of a pointer into the actual wide pointer:
/// the unsized tail `to` of the pointee was unsized from the sized type `from`.
#[derive(Debug, Clone, Copy)]
pub struct Unsize<'tcx> {
    pub from: Ty<'tcx>,
    pub to: Ty<'tcx>,
}

/// A byte of an evaluated constant, in the MiniRust sense.
#[derive(Debug, Clone, Copy)]
pub enum Byte<'tcx> {
    /// An uninitialized byte (e.g. padding, or the bytes of a union not covered by the active
    /// field).
    Uninit,
    /// A concrete byte value.
    Value(u8),
    /// A byte of a pointer into the given allocation. The `u8` is the index of this byte within the
    /// pointer.
    Ptr(AllocTarget<'tcx>, u8),
}

/// A global allocation. The host is in charge of naming it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GlobalRef {
    /// A static item.
    Static(DefId),
    /// An allocation without a corresponding item: an anonymous allocation, or a nested static
    /// (e.g. the `[1, 2]` in `static S: &[u8] = &[1, 2]`).
    Alloc(interpret::AllocId),
}

/// What an allocation stands for, from the point of view of pointers into it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AllocTarget<'tcx> {
    /// A function.
    Fn(ty::Instance<'tcx>),
    /// A global.
    Global(GlobalRef),
    /// A vtable. It's UB to read a vtable's data, so these are only reachable as provenance.
    VTable(Ty<'tcx>, &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>),
    /// The allocation backing a `TypeId`.
    TypeId(Ty<'tcx>),
}
