//@ charon-args=--mir=elaborated
//@ charon-args=--add-drop-bounds
fn use_string(_: String) {}

fn main() {
    let _s = String::new();
}
