//@ revisions=values,bytes
//@[values] charon-args=--consts=values
//@[bytes] charon-args=--consts=bytes
use std::mem::transmute;

trait Trait {}
impl Trait for u8 {}

struct Sy<T>(T);
unsafe impl<T> Sync for Sy<T> {}

const DYN: &(dyn Trait + Sync) = &0u8;
static DYN_REF: &(dyn Trait + Sync) = DYN;
static VTABLE: Sy<*const u8> =
    Sy(unsafe { transmute::<&(dyn Trait + Sync), [*const u8; 2]>(DYN)[1] });
