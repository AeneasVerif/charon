//! Trait elaboration: given a trait reference, we track which impl and/or local clauses caused it to be true.
#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

mod elaboration;
mod utils;

pub use elaboration::*;
pub use utils::*;

#[derive(Debug, Clone, Copy)]
pub struct BoundsOptions {
    /// Add `T: Destruct` bounds to every type generic, so that we can build `ImplExpr`s to know
    /// what code is run on drop.
    pub resolve_destruct: bool,
    /// Prune `T: Sized` and `T: MetaSized` predicates.
    pub prune_sized: bool,
}
