//@ known-failure
//@ revisions=poly,mono
//@ no-default-options
//@ charon-args=--mir built --raw-consts
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

// Mix an early-bound region with two different signature binders. Inheriting 'late must not
// shift the index of 'inner, and the innermost closure must resolve all three regions.
pub fn mixed_regions<'early, 'late, T: 'early>(x: &'early T, y: &'late T) {
    let f = for<'inner> |z: &'inner T| -> &'inner T {
        let g = || {
            let early: &'early T = x;
            let late: &'late T = y;
            let inner: &'inner T = z;
            (early, late, inner)
        };
        g();
        z
    };
    f(x);
}

// Inline constants inherit the same enclosing signature regions as closures.
pub fn inline_const<'a>(_x: &'a u32) -> Option<&'a u32> {
    const { None::<&'a u32> }
}

// Instantiate the generic case in mono mode as well.
pub fn exercise_mixed_regions() {
    mixed_regions(&0u32, &1u32);
    let _ = inline_const(&0);
}
