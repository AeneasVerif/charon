//@ aux-crate=start-from-attribute-dep-aux.rs
//@ charon-arg=--start-from-attribute
//! `--start-from-attribute` also selects the items of the dependencies outside the sysroot.
#![register_tool(verify)]
extern crate start_from_attribute_dep_aux;

#[verify::start_from]
fn local_model() -> u64 {
    7
}

fn dont_translate() {}
