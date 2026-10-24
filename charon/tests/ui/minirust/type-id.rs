//@ output=run-with-minirust
// `TypeId`s get made-up values in MiniRust, which must be equal exactly for equal types.
use std::any::{Any, TypeId};
use std::mem::transmute;

unsafe extern "Rust" {
    safe fn minirust_print(value: u32);
}

// FIXME: compare `TypeId`s directly once we translate the fallback body of `type_id_eq`.
fn bits<T: 'static>() -> u128 {
    unsafe { transmute(TypeId::of::<T>()) }
}

fn dyn_bits(x: &dyn Any) -> u128 {
    unsafe { transmute(x.type_id()) }
}

fn main() {
    minirust_print((bits::<u32>() == bits::<u32>()) as u32);
    minirust_print((bits::<u32>() == bits::<u8>()) as u32);
    minirust_print((bits::<u8>() == bits::<i8>()) as u32);
    minirust_print((dyn_bits(&42u32) == bits::<u32>()) as u32);
    minirust_print((dyn_bits(&42u32) == bits::<u8>()) as u32);
}
