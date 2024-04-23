//@ charon-args=--extract-opaque-bodies
//@ charon-args=--mir_optimized
//@ rustc-args=-C opt-level=3

fn call_is_some<T>(opt: Option<T>) -> bool {
    opt.is_some()
}

// This doesn't optimize to a bare discriminant read :(
fn my_is_some<T>(opt: Option<T>) -> isize {
    match opt {
        Some(_) => 1,
        None => 0,
    }
}
