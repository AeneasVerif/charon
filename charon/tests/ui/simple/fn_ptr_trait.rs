//@ known-failure
#![feature(fn_ptr_trait)]
fn requires_fn_ptr<F: std::marker::FnPtr>() {}

fn main() {
    requires_fn_ptr::<fn()>();
}
