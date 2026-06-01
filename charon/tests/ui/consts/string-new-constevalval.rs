//@ known-failure
//@ no-default-options
//@ charon-args=--raw-consts
//@ charon-args=--extract-opaque-bodies

pub fn mk_string() {
    let _ = String::new();
}
