//@ charon-args=--extract-opaque-bodies
//@ charon-args=--opaque core::intrinsics::copy_nonoverlapping::precondition_check
fn main() {
    let src = 1;
    let src_ptr: *const u32 = &src;
    let mut dst = 2;
    let dst_ptr: *mut u32 = &mut dst;
    unsafe { src_ptr.copy_to_nonoverlapping(dst_ptr, 1) };
}
