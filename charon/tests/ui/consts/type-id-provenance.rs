//@ revisions=values32,bytes32,values64,bytes64
//@[values32] charon-args=--consts=values
//@[values32] rustc-args=--target i686-unknown-linux-gnu
//@[values32] known-failure
//@[bytes32] charon-args=--consts=bytes
//@[bytes32] rustc-args=--target i686-unknown-linux-gnu
//@[values64] charon-args=--consts=values
//@[values64] rustc-args=--target x86_64-unknown-linux-gnu
//@[values64] known-failure
//@[bytes64] charon-args=--consts=bytes
//@[bytes64] rustc-args=--target x86_64-unknown-linux-gnu

use std::any::TypeId;
use std::mem::transmute;

// The number of pointers in a `TypeId`.
const N: usize = size_of::<TypeId>() / size_of::<*const u8>();

static TID: TypeId = TypeId::of::<u8>();
static TID_SWAPPED: TypeId = {
    let mut ptrs = unsafe { transmute::<TypeId, [*const u8; N]>(TypeId::of::<u8>()) };
    ptrs.swap(0, 1);
    unsafe { transmute::<[*const u8; N], TypeId>(ptrs) }
};
static mut TID_PTRS: [*const u8; N] = unsafe { transmute(TypeId::of::<u8>()) };
static mut TID_PTR_OFFSET: *const u8 = unsafe {
    transmute::<TypeId, [*const u8; N]>(TypeId::of::<u8>())[0].wrapping_add(size_of::<*const u8>())
};
