//@ charon-args=--consts=values
// Constant pointers into places whose type Charon can't compute from the type of the global:
// fields of associated types, and fields of opaque types.
use core::cell::UnsafeCell;

pub trait Tr {
    type S;
}
pub struct Inner {
    pub v: u32,
}
impl Tr for u8 {
    type S = Inner;
}
pub struct W<T: Tr>(pub T::S);
pub static X: W<u8> = W(Inner { v: 5 });
pub static P: &u32 = &X.0.v;

pub struct Sy<T>(pub T);
unsafe impl<T> Sync for Sy<T> {}
pub static CELL: Sy<UnsafeCell<(u8, u32)>> = Sy(UnsafeCell::new((1, 2)));
pub static CELL_FIELD: Sy<*mut u32> = Sy(unsafe { &raw mut (*CELL.0.get()).1 });
