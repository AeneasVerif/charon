//@ revisions=poly,mono
//@ known-failure
//@ charon-args=--mir built
//@[mono] charon-args=--monomorphize
#![feature(closure_lifetime_binder)]

// 'a is late-bound on the enclosing function, but explicitly named in the closure body.
pub fn local_annotation<'a>(x: &'a u32) -> u32 {
    let f = || {
        let y: &'a u32 = x;
        *y
    };
    f()
}

pub fn no_capture<'a>() {
    let f = || {
        let _: Option<&'a u32> = None;
    };
    f();
}

pub fn nested<'a>(x: &'a u32) -> u32 {
    let f = || {
        let g = || {
            let y: &'a u32 = x;
            *y
        };
        g()
    };
    f()
}

pub fn enclosing_closure() -> u32 {
    let f = for<'a> |x: &'a u32| -> u32 {
        let g = || {
            let y: &'a u32 = x;
            *y
        };
        g()
    };
    f(&42)
}
