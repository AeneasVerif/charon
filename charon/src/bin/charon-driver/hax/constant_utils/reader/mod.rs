//! Reading evaluated constants back.
use super::super::*;
use rustc_const_eval::const_eval;
use rustc_const_eval::interpret::{FnVal, InterpResult, interp_ok};
use rustc_middle::mir::interpret;
use rustc_middle::{mir, ty};

mod memory;
pub(crate) use memory::*;

/// A global allocation. The host is in charge of naming it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GlobalRef {
    /// A static item.
    Static(RDefId),
    /// An allocation without a corresponding item: an anonymous allocation, or a nested static
    /// (e.g. the `[1, 2]` in `static S: &[u8] = &[1, 2]`).
    Alloc(interpret::AllocId),
}

/// What an allocation stands for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AllocTarget<'tcx> {
    /// A function.
    Fn(ty::Instance<'tcx>),
    /// A global.
    Global(GlobalRef),
    /// A vtable. It's UB to read a vtable's data, so these are only reachable as provenance.
    VTable(
        ty::Ty<'tcx>,
        &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    ),
    /// The allocation backing a `TypeId`.
    TypeId(ty::Ty<'tcx>),
}

/// Classify the given allocation.
fn alloc_target<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    alloc_id: interpret::AllocId,
) -> AllocTarget<'tcx> {
    use interpret::GlobalAlloc;
    let tcx = s.base().tcx;
    match tcx.global_alloc(alloc_id) {
        GlobalAlloc::Function { instance } => AllocTarget::Fn(instance),
        GlobalAlloc::Static(def_id)
            if let rustc_hir::def::DefKind::Static { nested: false, .. } = tcx.def_kind(def_id) =>
        {
            AllocTarget::Global(GlobalRef::Static(def_id))
        }
        GlobalAlloc::Static(_) | GlobalAlloc::Memory(_) => {
            AllocTarget::Global(GlobalRef::Alloc(alloc_id))
        }
        GlobalAlloc::VTable(ty, preds) => AllocTarget::VTable(ty, preds),
        GlobalAlloc::TypeId { ty } => AllocTarget::TypeId(ty),
    }
}

/// Whether we refer to `global` by name in pointers to it, rather than inlining its contents.
pub(crate) fn is_named_global<'tcx, S: UnderOwnerState<'tcx>>(s: &S, global: GlobalRef) -> bool {
    match global {
        GlobalRef::Static(_) => true,
        // TODO: nested statics are synthetic items that make the rest of the machinery ICE, so we
        // don't name them yet.
        GlobalRef::Alloc(alloc_id) => {
            s.base().options.anon_allocs_as_globals
                && matches!(
                    s.base().tcx.global_alloc(alloc_id),
                    interpret::GlobalAlloc::Memory(_)
                )
        }
    }
}

/// A constant that we can ask rustc to evaluate.
#[derive(Debug, Clone, Copy)]
pub enum ConstSource<'tcx> {
    /// An already-evaluated constant, e.g. found in MIR.
    Value(mir::ConstValue, ty::Ty<'tcx>),
}

/// How to read back an evaluated constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReadMode {
    /// As a structured value (literals, ADTs, references...).
    Structured,
    /// As raw bytes (`ConstantExprKind::Memory`).
    Bytes,
}
