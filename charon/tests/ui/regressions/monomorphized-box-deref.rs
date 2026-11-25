//@ known-failure
//@ no-default-options
//@ charon-args=--sysroot=default --mir=elaborated --monomorphize --treat-box-as-builtin

// Elaborated MIR projects through Box's fields. In monomorphized mode, the Box
// type reference has no generic arguments, triggering generics.types.len() == 2.
pub fn deref_box(b: Box<u32>) -> u32 {
    *b
}
