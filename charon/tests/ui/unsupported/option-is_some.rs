//@ known-failure
//@ charon-args=--extract-opaque-bodies

// Panics because the optimized MIR has a discriminant read not followed by a SwitchInt.
fn my_is_some<T>(opt: Option<T>) -> bool {
    opt.is_some()
}
