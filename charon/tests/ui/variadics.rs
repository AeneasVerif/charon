#![feature(c_variadic)]

pub unsafe extern "C" fn sum(mut ap: ...) -> i32 {
    let a: i32 = ap.next_arg();
    let b: i32 = ap.next_arg();
    a + b
}

extern "C" {
    fn foo(x: u32, y: u64, rest: ...);
}

pub fn call() {
    let _ = unsafe { sum(1i32, 2i32) };
    let _ = unsafe { foo(1, 2, 3, 4, 5) };
    let fn_ptr: unsafe extern "C" fn(u32, u64, ...) = foo;
    let _ = unsafe { fn_ptr(1, 2, 3, 4, 5) };
}
