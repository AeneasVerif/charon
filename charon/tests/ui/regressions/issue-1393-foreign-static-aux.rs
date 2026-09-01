//@ ignore
// A `static mut`, like a static whose type has interior mutability (`Cell`, `RefCell`, atomics...),
// gets a *mutable* allocation.
pub static mut MUTABLE: u8 = 42;

// A static holding a pointer with no provenance, which therefore can't be dereferenced.
pub struct Wrapper(pub *const u8);
unsafe impl Sync for Wrapper {}
pub static DANGLING: Wrapper = Wrapper(4 as *const u8);

// A "trivial" const in a generic impl: rustc stores its value directly and encodes no MIR for it,
// and const-evaluating it fails because the item isn't monomorphic.
pub struct Generic<T, const N: usize>(pub T);
impl<T, const N: usize> Generic<T, N> {
    pub const TRIVIAL: u8 = 128;
}
