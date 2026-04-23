#![allow(rustdoc::private_intra_doc_links)]

mod rustc_utils;
pub mod state;
mod utils;

mod constant_utils;
mod types;

mod index_vec;
mod prelude;

pub use prelude::*;

mod sinto;
mod traits;

pub use hax_adt_into::AdtInto;
pub use sinto::SInto;

pub mod options {
    #[derive(Debug, Clone)]
    pub struct Options {
        /// Whether we should evaluate and inline the value of anonymous constants (inline `const {}`
        /// blocks or advanced constant expressions as in `[T; N+1]`), or refer to them as
        /// `GlobalName`s.
        pub inline_anon_consts: bool,
        /// Options related to bounds.
        pub bounds_options: BoundsOptions,
    }

    #[derive(Debug, Clone, Copy)]
    pub struct BoundsOptions {
        /// Add `T: Destruct` bounds to every type generic, so that we can build `ImplExpr`s to know
        /// what code is run on drop.
        pub resolve_destruct: bool,
        /// Prune `T: Sized` and `T: MetaSized` predicates.
        pub prune_sized: bool,
    }
}
