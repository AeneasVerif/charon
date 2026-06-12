//@ no-default-options
//@ charon-args=--raw-consts

const DISGUISED_INT: *const () = 42 as _;

pub fn pointer_pattern() {
    match 43 as *const () {
        DISGUISED_INT => {}
        _ => {}
    }
}
