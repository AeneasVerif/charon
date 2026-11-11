//@ aux-crate=link-extern-fns-aux.rs
//@ charon-args=--start-from=crate::sys
//@ charon-args=--start-from=alloc::alloc::__rust_alloc
//@ charon-args=--start-from=core::panicking::panic_fmt --include=core::panicking::panic_fmt
//@ rustc-args=--crate-type=bin
extern crate link_extern_fns_aux;

mod sys {
    unsafe extern "Rust" {
        pub fn local_hook(x: u32) -> u32;
        pub fn dep_hook() -> u8;
    }
    unsafe extern "C" {
        pub fn weak_hook() -> u8;
    }
}

#[unsafe(no_mangle)]
fn local_hook(x: u32) -> u32 {
    x + 1
}

fn main() {}
