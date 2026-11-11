//@ charon-args=--start-from=alloc::alloc::__rust_alloc
//@ rustc-args=--crate-type=bin
use std::alloc::{GlobalAlloc, Layout};

struct Null;

unsafe impl GlobalAlloc for Null {
    unsafe fn alloc(&self, _: Layout) -> *mut u8 {
        0 as *mut u8
    }
    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {}
}

#[global_allocator]
static A: Null = Null;

fn main() {}
