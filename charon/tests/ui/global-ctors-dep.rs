//@ aux-crate=global-ctors-dep-aux.rs
//@ charon-args=--start-from-global-ctors
//@ charon-args=--extract-opaque-bodies --consts values
//@ rustc-args=--crate-type=bin --target=x86_64-unknown-linux-gnu
//! The global constructors of linked dependencies are picked up too.
extern crate global_ctors_dep_aux;

fn main() {}
