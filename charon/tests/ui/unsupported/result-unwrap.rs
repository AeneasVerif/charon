//@ known-failure
//@ no-check-output
//@ charon-args=--extract-opaque-bodies

// Errors because dyn types are not supported.
fn unwrap(res: Result<u32, u32>) -> u32 {
    res.unwrap()
}
