//@ revisions=poly,mono
//@ charon-args=--mir optimized
//@[mono] charon-args=--monomorphize
#![feature(core_intrinsics, ptr_metadata)]
#![allow(internal_features)]

pub fn metadata<T: ?Sized>(ptr: *const T) -> <T as std::ptr::Pointee>::Metadata {
    std::intrinsics::ptr_metadata(ptr)
}

trait Trait {}
impl Trait for u32 {}

fn main() {
    let _ = metadata(&42u32);
    let _ = metadata(&[1u32, 2][..]);
    let _ = metadata(&42u32 as &dyn Trait);
}
