//@ charon-args=--consts=values --raw-consts
// References to anonymous allocations.
use std::mem::MaybeUninit;

struct Sync<T>(T);
unsafe impl<T> std::marker::Sync for Sync<T> {}

// An allocation referenced at a type that covers it, then into its middle.
static BYTES: &[u8; 4] = &[1, 2, 3, 4];
static SECOND: Sync<*const u8> = Sync(unsafe { BYTES.as_ptr().add(1) });

// An allocation referenced first at a type that doesn't cover it.
static HALF: Sync<*const u16> = Sync(&raw const PAIR.0);
static PAIR: &(u16, u16) = &(5, 6);

// An allocation referenced first from raw memory.
static RAW: MaybeUninit<&(u8, u8)> = MaybeUninit::new(&(7, 8));
static RAW_REF: &(u8, u8) = unsafe { RAW.assume_init() };

// Equal promoted constants.
pub fn first() -> &'static [u32; 3] {
    &[1, 2, 3]
}
pub fn second() -> &'static [u32; 3] {
    &[1, 2, 3]
}
pub fn third() -> &'static (u8, u32) {
    &(1, 2)
}
pub fn fourth() -> &'static (u8, u32) {
    &(1, 2)
}
