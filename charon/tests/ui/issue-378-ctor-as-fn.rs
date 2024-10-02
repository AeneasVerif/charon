//@ known-failure

static F: fn(u8) -> Option<u8> = Some;

fn main() {
    let f: fn(u8) -> _ = Some;
    let _ = f(42);
}

enum Foo<'a, T> {
    Variant(&'a T),
}
