//@ charon-args=--consts=values --monomorphize

trait HasLen {
    const LEN: usize;
}

impl<T, const N: usize> HasLen for [T; N] {
    const LEN: usize = N;
}

pub fn use_len() -> usize {
    <[u8; 4] as HasLen>::LEN
}

trait HasSize {
    const SIZE: usize;
}

impl<T> HasSize for T {
    const SIZE: usize = core::mem::size_of::<T>();
}

pub fn use_size() -> usize {
    <u8 as HasSize>::SIZE + <u64 as HasSize>::SIZE + <[u32; 3] as HasSize>::SIZE
}
