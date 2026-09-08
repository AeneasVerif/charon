//@ charon-args=--monomorphize

static BAR: fn(i32) = |a| assert_ne!(a, 43);

fn foo<T>() {
    let c = |a: i32| assert_ne!(a, 43);
    c(42);
}

fn main() {
    let boo: &dyn Fn(i32) = &BAR;
    boo(42);
    foo::<u8>();
}
