use std::mem::MaybeUninit;

pub fn repeat_inline_const<T, const N: usize>() -> [MaybeUninit<T>; N] {
    [const { MaybeUninit::uninit() }; N]
}

pub struct NonCopy(u32);

const VALUE: NonCopy = NonCopy(42);

pub fn repeat_named_const<const N: usize>() -> [NonCopy; N] {
    [VALUE; N]
}

pub fn repeat_zero(value: NonCopy) -> [NonCopy; 0] {
    [value; 0]
}

pub fn repeat_one(value: NonCopy) -> [NonCopy; 1] {
    [value; 1]
}

pub fn repeat_copy<T: Copy, const N: usize>(value: T) -> [T; N] {
    [value; N]
}
