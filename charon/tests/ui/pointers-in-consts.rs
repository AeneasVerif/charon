//@ revisions=default,no-warns
//@[no-warns] ignore-warnings
const DISGUISED_INT: *const () = 42 as _;

pub fn bar() {
    match 43 as *const () {
        DISGUISED_INT => {}
        _ => {}
    }
}
