#![feature(fn_static)]
fn requires_fn_ptr<F: std::ops::FnPtr>() {}

fn main() {
    requires_fn_ptr::<fn()>();
}
