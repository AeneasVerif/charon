//@ ignore
pub struct Sync<T>(pub T);
unsafe impl<T> std::marker::Sync for Sync<T> {}

pub static ARR: [u32; 3] = [1, 2, 3];
// One past the end: an offset.
pub static END: Sync<*const u32> = Sync(unsafe { (&raw const ARR).cast::<u32>().add(3) });
// A misaligned offset, by bytes.
pub static BYTE: Sync<*const u16> = Sync(unsafe { (&raw const ARR).cast::<u8>().add(3).cast() });
// A wrapping out-of-bounds pointer.
pub static OOB: Sync<*const u32> = Sync((&raw const ARR).cast::<u32>().wrapping_sub(1));
// A pointer to a function.
pub fn foo() -> u8 {
    1
}
pub static FN_RAW: Sync<*const ()> = Sync(foo as fn() -> u8 as *const ());
