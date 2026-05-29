#![feature(ptr_metadata)]
use std::ptr::Pointee;

fn assert_copy<T: Copy>() {}

fn foo<T: ?Sized>() {
    assert_copy::<<T as Pointee>::Metadata>()
}
