//@ revisions=default,raw
//@ charon-args=--start-from=crate::main
//@[raw] charon-args=--raw-consts
#![feature(adt_const_params, unsized_const_params)]

#[derive(std::marker::ConstParamTy, PartialEq, Eq)]
struct Wrap<T: ?Sized>(u8, T);

const WRAP: &Wrap<[u8]> = &Wrap(5, [97, 98]);
const STR_TAIL: &Wrap<str> = unsafe { &*(WRAP as *const Wrap<[u8]> as *const Wrap<str>) };

fn str_tail<const W: &'static Wrap<str>>() {}

fn main() {
    let _ = "hello";
    str_tail::<STR_TAIL>();
}
