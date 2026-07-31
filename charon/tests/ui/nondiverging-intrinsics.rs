//@ charon-args=--mir optimized
#![feature(core_intrinsics)]
#![allow(internal_features)]

unsafe fn intrinsic_statements<T>(condition: bool, src: *const T, dst: *mut T, count: usize) {
    unsafe {
        core::intrinsics::assume(condition);
        core::intrinsics::copy_nonoverlapping(src, dst, count);
    }
}
