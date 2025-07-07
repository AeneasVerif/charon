//@ charon-args=--add-drop-bounds
//@ known-failure
fn foo<T>(x: T) {
    let _ = || drop(x);
}

fn bar() {
    let x = || {};
}
