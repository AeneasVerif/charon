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
// For rustdoc: prevents overflows
#![recursion_limit = "256"]
#![feature(box_patterns)]
#![feature(if_let_guard)]
#![feature(impl_trait_in_assoc_type)]
#![feature(iterator_try_collect)]
#![feature(let_chains)]
#![feature(lint_reasons)]
#![feature(trait_alias)]
#![feature(register_tool)]
// For when we use charon on itself :3
#![register_tool(charon)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_error_messages;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

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

// Re-export all the ast modules so we can keep the old import structure.
pub use ast::{assumed, expressions, gast, llbc_ast, meta, names, types, ullbc_ast, values};
pub use pretty::formatter;
pub use transform::{graphs, reorder_decls, ullbc_to_llbc};

/// The version of the crate, as defined in `Cargo.toml`.
const VERSION: &str = env!("CARGO_PKG_VERSION");
