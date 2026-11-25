//@ no-default-options
//@ charon-args=--sysroot=default --mir=elaborated --monomorphize --treat-box-as-builtin

// Elaborated MIR projects through Box's fields. Reconstructing a dereference
// must also work when the Box type reference has no generic arguments in mono mode.
pub fn deref_box(b: Box<u32>) -> u32 {
    *b
}
