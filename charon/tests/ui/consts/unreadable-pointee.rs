//@ known-failure
//@ charon-args=--consts=values
// The pointee of this pointer is too big to have a layout, so we can't read it.
pub struct Wrapper(*const [u8]);
unsafe impl Sync for Wrapper {}

pub static HUGE: Wrapper = Wrapper(std::ptr::slice_from_raw_parts(&0u8, usize::MAX));
