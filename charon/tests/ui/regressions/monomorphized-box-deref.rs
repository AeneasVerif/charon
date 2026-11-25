//@ charon-args=--mir=elaborated --monomorphize --treat-box-as-builtin
// Box deref reconstruction used to panic in mono mode because then `Box` gets monomorphized and
// takes no generics.
pub fn deref_box(b: Box<u32>) -> u32 {
    *b
}
