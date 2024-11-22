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

// For rustdoc: prevents overflows
#![recursion_limit = "256"]
#![feature(box_patterns)]
#![feature(deref_pure_trait)]
#![feature(extract_if)]
#![feature(if_let_guard)]
#![feature(impl_trait_in_assoc_type)]
#![feature(iterator_try_collect)]
#![feature(let_chains)]
#![feature(trait_alias)]
#![feature(register_tool)]
// For when we use charon on itself :3
#![register_tool(charon)]

#[macro_use]
pub mod ids;
#[macro_use]
pub mod logger;
pub mod ast;
pub mod common;
pub mod errors;
pub mod export;
pub mod name_matcher;
pub mod options;
pub mod pretty;
pub mod transform;

// Re-export all the ast modules so we can keep the old import structure.
pub use ast::{builtins, expressions, gast, llbc_ast, meta, names, types, ullbc_ast, values};
pub use pretty::formatter;
pub use transform::{graphs, reorder_decls, ullbc_to_llbc};

/// The version of the crate, as defined in `Cargo.toml`.
const VERSION: &str = env!("CARGO_PKG_VERSION");
