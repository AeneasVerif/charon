//@ known-failure
//@ charon-args=--mir_promoted
fn f<T>() {
    // This can't be evaluated generically.
    let _ = &size_of::<T>();
}
