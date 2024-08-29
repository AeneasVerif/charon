//@ known-failure
//@ no-check-output

fn foo() {
    let x: *const _ = std::ptr::null::<u32>();
    let _ = unsafe { *x };
}

unsafe trait Trait {}

unsafe impl Trait for () {}

static mut COUNTER: usize = 0;

fn increment() {
    unsafe {
        COUNTER += 1;
    }
}
