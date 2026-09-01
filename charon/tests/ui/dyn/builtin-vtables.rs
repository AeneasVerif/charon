//@ charon-args=--include=core::ops::function
fn takes_fn(_: &dyn Fn(u32) -> u32) {}

fn some_fn(x: u32) -> u32 {
    x
}

fn generic_fn<T>(x: T) -> T {
    x
}

fn main() {
    takes_fn(&some_fn);
    takes_fn(&|_| 42);
    // The `Fn*` impls of an instantiated generic fn item.
    takes_fn(&generic_fn::<u32>);
}
