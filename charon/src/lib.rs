//! This library contains the definitions of the "LLBC" (Low-Level Borrow Calculus)
//! AST, which faithfully captures the full and explicit contents of a Rust crate.
//! The `charon` binary can translate any Rust crate to this AST, which can then be consumed for
//! all sorts of purposes (most notably analysis, code generation, and execution).
//!
//! The main type of this crate is [`ast::TranslatedCrate`].
//! To get one, call `charon` to get a serialized crate, then deserialize it using using
//! [`deserialize_llbc`].
//! A crate is mainly composed of 5 kinds of items:
//! - Functions;
//! - Type definitions;
//! - Globals (constants and statics);
//! - Trait declarations;
//! - Trait implementations.
//!
//! Each of these items is identified internally by a unique [`ast::ItemId`],
//! and externally by its [`ast::Name`], such as "`core::result::Result`".
//! To find an item with a given name, have a look at the name matcher [`name_matcher::Pattern`]s.
//!
//! Function bodies come in two forms: "structured" or "unstructured", depending on whether their
//! control-flow is syntax-like (with blocks and scopes) or control-flow-like (with gotos).
//! This can be chosen during translation. The corresponding ASTs can be found respectively in
//! [`llbc_ast`] and [`ullbc_ast`].
// For rustdoc: prevents overflows
#![recursion_limit = "256"]
#![allow(
    clippy::borrowed_box,
    clippy::derivable_impls,
    clippy::field_reassign_with_default,
    clippy::manual_map,
    clippy::mem_replace_with_default,
    clippy::new_ret_no_self,
    clippy::new_without_default,
    clippy::should_implement_trait,
    clippy::useless_format
)]
// For when we use charon on itself :3
#![cfg_attr(feature = "charon_on_charon", feature(register_tool))]
#![cfg_attr(feature = "charon_on_charon", register_tool(charon))]

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

/// The version of the crate, as defined in `Cargo.toml`.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Read a `.llbc` file.
pub fn deserialize_llbc(path: &std::path::Path) -> anyhow::Result<ast::TranslatedCrate> {
    deserialize_llbc_with_format(path, options::SerializationFormat::Json)
}

/// Read a serialized (U)LLBC file.
pub fn deserialize_llbc_with_format(
    path: &std::path::Path,
    format: options::SerializationFormat,
) -> anyhow::Result<ast::TranslatedCrate> {
    use crate::export::CrateData;
    Ok(CrateData::deserialize_from_file(path, format)?.translated)
}
