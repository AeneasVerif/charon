//! This library contains utilities to extract the MIR from a Rust project,
//! by compiling it to an easy-to-use AST called LLBC (Low-Level Borrow Calculus).
//! This AST is serialized into JSON files.
//!
//! A good entry point to explore the project is [`driver`](driver),
//! and in particular [`driver::CharonCallbacks`](driver::CharonCallbacks),
//! which implements the callback which we provide to Rustc.
//!
//! The ASTs are in [`ullbc_ast`](ullbc_ast) (Unstructured LLBC - basically
//! a cleaned-up version of MIR) and [`llbc_ast`](llbc_ast) (same as ULLBC, but
//! we reconstructed the control-flow to have `if ... then ... else ...`,
//! loops, etc. instead of `GOTO`s).

#![feature(rustc_private)]
#![feature(box_patterns)]
// For rustdoc: prevents overflows
#![recursion_limit = "256"]
#![feature(trait_alias)]
#![feature(let_chains)]
#![feature(if_let_guard)]
#![feature(iterator_try_collect)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_attr;
extern crate rustc_error_messages;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

#[macro_use]
pub mod ids;
#[macro_use]
pub mod logger;
pub mod ast;
pub mod cli_options;
pub mod common;
pub mod deps_errors;
pub mod export;
pub mod pretty;
pub mod transform;
pub mod translate;

// Re-export all the ast modules so we can keep the old import structure.
pub use ast::{
    assumed, expressions, expressions_utils, gast, gast_utils, llbc_ast, llbc_ast_utils, meta,
    meta_utils, names, names_utils, types, types_utils, ullbc_ast, ullbc_ast_utils, values,
    values_utils,
};
pub use pretty::formatter;
pub use transform::{graphs, reorder_decls, ullbc_to_llbc};
pub use translate::{
    get_mir, translate_constants, translate_crate_to_ullbc, translate_ctx,
    translate_functions_to_ullbc, translate_predicates, translate_traits, translate_types,
};

/// The version of the crate, as defined in `Cargo.toml`.
const VERSION: &str = env!("CARGO_PKG_VERSION");
