//@ charon-args=--extract-opaque-bodies
//@ charon-args=--exclude=core
//@ charon-args=--include=core::slice --include=core::slice::index::*
//@ charon-args=--include=core::option::Option
pub fn slice_index_range(slice: &[u8]) -> &[u8] {
    &slice[0..=10]
}
