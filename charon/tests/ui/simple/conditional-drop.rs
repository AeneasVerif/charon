//@ charon-args=--mir=elaborated
fn use_string(_: String) {}

fn main() {
    let s = String::new();
    if false {
        use_string(s);
    }
    // `s` is dropped implicitly here
}
