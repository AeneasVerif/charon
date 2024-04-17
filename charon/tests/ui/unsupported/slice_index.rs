//@ known-panic
//@ no-check-output
//@ charon-args=--extract-opaque-bodies

// hax panics when lowering a place expression.
fn slice_index(slice: &[u8]) {
    let _ = &slice[0..=10];
}
