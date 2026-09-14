//@ known-failure
use std::mem::MaybeUninit;

pub fn repeat_inline_const<T, const N: usize>() -> [MaybeUninit<T>; N] {
    [const { MaybeUninit::uninit() }; N]
}
