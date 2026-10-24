//! Evaluate constants with `rustc_const_uneval` in the current context.
use crate::hax::prelude::*;
use annotate_snippets::Level;
use rustc_const_uneval::{ConstReader, ReadError};

sinto_reexport!(rustc_abi::VariantIdx);

pub use rustc_const_uneval::{ConstSource, GlobalRef, ReadMode};

/// The reader for constants evaluated in the current context.
pub fn const_reader<'tcx, S: UnderOwnerState<'tcx>>(s: &S) -> ConstReader<'tcx> {
    ConstReader {
        tcx: s.base().tcx,
        typing_env: s.typing_env(),
        config: s.base().options.consts,
    }
}

/// The global standing for `self`, which must be named (see `ConstReader::is_named_global`).
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ItemRef<'tcx>> for GlobalRef {
    fn sinto(&self, s: &S) -> ItemRef<'tcx> {
        match *self {
            GlobalRef::Static(did) => translate_item_ref(s, did, Default::default()),
            GlobalRef::Alloc(alloc_id) => {
                let def_id = DefId::make_anon_alloc(s, alloc_id);
                ItemRef::dummy_without_generics(s, def_id)
            }
        }
    }
}

/// Evaluate `src` and read it back.
pub fn read_const<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    span: rustc_span::Span,
    src: ConstSource<'tcx>,
    mode: ReadMode,
) -> Option<rustc_const_uneval::Const<'tcx>> {
    match const_reader(s).read(span, src, mode) {
        Ok(val) => Some(val),
        Err(ReadError::NotEvaluable) => None,
        Err(err) => {
            s.raise(
                Level::WARNING,
                span,
                format!("Couldn't convert constant {src:?} back to an expression: {err:?}"),
            );
            None
        }
    }
}
