#![allow(unused)]

#[derive(Clone, Copy)]
struct Foo;
fn copy_foo(x: Foo) {
    let y = x;
    let z = x;
}

fn copy_generic<T: Copy>(x: T) {
    let y = x;
    let z = x;
}

trait Trait {
    type Ty: Copy;
}
fn copy_assoc_ty<T: Trait>(x: T::Ty) {
    let y = x;
    let z = x;
}

trait Supertrait: Copy {}
fn copy_supertrait<T: Supertrait>(x: T) -> (T, T) {
    (x, x)
}

fn copy_array<T: Copy, const N: usize>(x: [T; N]) -> ([T; N], [T; N]) {
    (x, x)
}

fn copy_shared_ref<T: ?Sized>(x: &T) -> (&T, &T) {
    (x, x)
}

fn copy_fn_ptr(x: for<'a> fn(&'a u32) -> &'a u32) {
    let y = x;
    let z = x;
}
