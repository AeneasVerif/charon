//@ known-panic
//@ no-check-output
fn main() {
    let slice: &[i32] = &[0];
    let _ = slice.iter().next();
}
