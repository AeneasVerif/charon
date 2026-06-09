//@ no-default-options
//@ charon-args=--extract-opaque-bodies
//@ charon-args=--mir elaborated
//@ charon-args=--exclude=core
//@ charon-args=--include=core::result::Result
//@ charon-args=--include=core::marker::Destruct
//@ charon-args=--include=core::alloc
//@ charon-args=--include=core::mem
//@ charon-args=--include=core::ptr
//@ charon-args=--exclude=alloc::alloc

unsafe fn foo() {
    let b = Box::new(42);
    let p = Box::into_raw(b);
    let _ = Box::leak(Box::new(42));
    let mut b = Box::from_raw(p);
    let i = *b;
    *b = 42;
}
