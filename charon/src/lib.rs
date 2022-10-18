#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![feature(is_some_with)]
#![feature(cell_leak)] // For Ref::leak
// For rustdoc: prevents overflows
#![recursion_limit = "256"]

extern crate hashlink;
extern crate im;
extern crate linked_hash_set;
extern crate log;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_const_eval;
extern crate rustc_driver;
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
mod common;
mod assumed;
mod cli_options;
mod divergent;
mod driver;
mod expressions;
mod expressions_utils;
mod extract_global_assignments;
mod formatter;
mod generics;
mod get_mir;
mod graphs;
mod id_vector;
mod insert_assign_return_unit;
mod llbc_ast;
mod llbc_ast_utils;
mod llbc_export;
mod logger;
mod names;
mod names_utils;
mod reconstruct_asserts;
mod regions_hierarchy;
mod register;
mod regularize_constant_adts;
mod remove_unused_locals;
mod reorder_decls;
mod rust_to_local_ids;
mod simplify_ops;
mod translate_functions_to_im;
mod translate_types;
mod types;
mod types_utils;
mod ullbc_ast;
mod ullbc_ast_utils;
mod ullbc_to_llbc;
mod values;
mod values_utils;
