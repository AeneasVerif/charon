//@ known-failure
//@ no-default-options
//@ charon-args=--raw-consts
//@ charon-args=--extract-opaque-bodies
//@ charon-args=--exclude=core
//@ charon-args=--exclude=alloc::alloc
//@ charon-args=--exclude=alloc::raw_vec

pub fn mk_string() {
    let _ = String::new();
}
