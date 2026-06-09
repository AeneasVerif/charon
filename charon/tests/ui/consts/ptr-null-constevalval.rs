//@ no-default-options
//@ charon-args=--raw-consts
//@ charon-args=--extract-opaque-bodies
//@ charon-args=--monomorphize
//@ charon-args=--exclude=core::fmt

pub fn null_ptr() {
    let _ = core::ptr::null::<u8>();
}
