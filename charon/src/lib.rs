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

#![feature(rustc_private, register_tool)]
#![feature(box_patterns)]
// For rustdoc: prevents overflows
#![recursion_limit = "256"]
#![feature(trait_alias)]
#![feature(let_chains)]
#![feature(iterator_try_collect)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_attr;
extern crate rustc_driver;
extern crate rustc_error_messages;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

#[macro_use]
pub mod ids;
#[macro_use]
pub mod logger;
pub mod assumed;
pub mod ast;
pub mod cli_options;
pub mod common;
pub mod deps_errors;
pub mod driver;
pub mod export;
pub mod get_mir;
pub mod graphs;
pub mod pretty;
pub mod reorder_decls;
pub mod transform;
pub mod translate;
pub mod ullbc_to_llbc;

// Re-export all the ast modules so we can keep the old import structure.
pub use crate::pretty::formatter;
pub use ast::{
    expressions, expressions_utils, gast, gast_utils, llbc_ast, llbc_ast_utils, meta, meta_utils,
    names, names_utils, types, types_utils, ullbc_ast, ullbc_ast_utils, values, values_utils,
};
pub use translate::{
    translate_constants, translate_crate_to_ullbc, translate_ctx, translate_functions_to_ullbc,
    translate_predicates, translate_traits, translate_types,
};
