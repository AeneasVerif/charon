//@ known-failure
pub fn identity<T>(value: T) -> T {
    let _closure = || ();
    value
}

pub fn main() {
    let _ = Some(42).map(identity);
}
