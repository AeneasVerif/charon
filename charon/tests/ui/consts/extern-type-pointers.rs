//@ revisions=values,bytes
//@[values] charon-args=--consts=values
//@[bytes] charon-args=--consts=bytes
//@ ignore-warnings
//@[values] known-failure
// Pointers to an extern type.
#![feature(extern_types)]
#![allow(unused)]
struct Sync<T>(T);
unsafe impl<T> core::marker::Sync for Sync<T> {}

unsafe extern "C" {
    type Opaque;
}
static X: u8 = 0;
static EXTERN: Sync<*const Opaque> = Sync(&X as *const u8 as *const Opaque);
static EXTERN_NO_PROVENANCE: Sync<*const Opaque> = Sync(8 as *const Opaque);

fn main() {}
