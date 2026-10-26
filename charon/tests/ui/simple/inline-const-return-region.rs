//@ no-default-options
//@ charon-args=--mir=promoted --raw-consts
// Keep the inline const visible to track the lifetime in its inferred return type.
pub fn foo<'a>() -> Option<&'a u8> {
    const { None }
}
