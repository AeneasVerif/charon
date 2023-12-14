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
#![feature(cell_leak)] // For Ref::leak
// For rustdoc: prevents overflows
#![recursion_limit = "256"]
#![feature(trait_alias)]
#![feature(let_chains)]
#![feature(iterator_try_collect)]
#![feature(associated_type_defaults)]

extern crate hashlink;
extern crate im;
extern crate linked_hash_set;
extern crate log;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_const_eval;
extern crate rustc_driver;
extern crate rustc_error_messages;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_mir_transform;
extern crate rustc_monomorphize;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate take_mut;

#[macro_use]
pub mod common;
pub mod assumed;
pub mod cli_options;
pub mod deps_errors;
pub mod driver;
pub mod export;
pub mod expressions;
pub mod expressions_utils;
pub mod formatter;
pub mod gast;
pub mod gast_utils;
pub mod get_mir;
pub mod graphs;
pub mod id_map;
pub mod id_vector;
pub mod index_to_function_calls;
pub mod insert_assign_return_unit;
pub mod llbc_ast;
pub mod llbc_ast_utils;
pub mod logger;
pub mod meta;
pub mod meta_utils;
pub mod names;
pub mod names_utils;
pub mod ops_to_function_calls;
pub mod reconstruct_asserts;
pub mod remove_drop_never;
pub mod remove_dynamic_checks;
pub mod remove_nops;
pub mod remove_read_discriminant;
pub mod remove_unused_locals;
pub mod reorder_decls;
pub mod simplify_constants;
pub mod translate_constants;
pub mod translate_crate_to_ullbc;
pub mod translate_ctx;
pub mod translate_functions_to_ullbc;
pub mod translate_predicates;
pub mod translate_traits;
pub mod translate_types;
pub mod types;
pub mod types_utils;
pub mod ullbc_ast;
pub mod ullbc_ast_utils;
pub mod ullbc_to_llbc;
pub mod update_closure_signatures;
pub mod values;
pub mod values_utils;
