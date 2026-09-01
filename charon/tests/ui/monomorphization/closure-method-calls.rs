//@ charon-args=--monomorphize
//@ charon-args=--start-from=crate::main

fn apply(f: impl Fn(i32) -> i32, x: i32) -> i32 {
    f(x)
}

fn apply_mut(mut f: impl FnMut(i32) -> i32, x: i32) -> i32 {
    f(x)
}

fn apply_once(f: impl FnOnce(i32) -> i32, x: i32) -> i32 {
    f(x)
}

fn plain(x: i32) -> i32 {
    x + 1
}

fn main() {
    apply(|x| x + 1, 1);
    apply_mut(|x| x + 1, 1);
    apply_once(|x| x + 1, 1);
    apply(plain, 1);
    apply_mut(plain, 1);
    apply_once(plain, 1);
}
