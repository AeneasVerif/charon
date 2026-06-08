//@ charon-args=--evaluate-consts --monomorphize --targets=x86_64-unknown-linux-gnu,i686-unknown-linux-gnu

trait HasSize {
    const SIZE: usize;
}

impl<T> HasSize for T {
    const SIZE: usize = core::mem::size_of::<T>();
}

const USIZE_SIZE: usize = <usize as HasSize>::SIZE;

pub fn usize_size() -> usize {
    <usize as HasSize>::SIZE
}
