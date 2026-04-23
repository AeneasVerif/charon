#![allow(rustdoc::private_intra_doc_links)]
#![feature(if_let_guard)]
#![feature(macro_metavar_expr)]
#![feature(rustc_private)]
#![feature(sized_hierarchy)]
#![feature(trait_alias)]
#![feature(type_changing_struct_update)]

extern crate rustc_abi;
extern crate rustc_apfloat;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_const_eval;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hashes;
extern crate rustc_hir;
extern crate rustc_hir_analysis;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_lexer;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

mod rustc_utils;
pub mod state;
mod utils;

mod constant_utils;
pub mod id_table;
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
