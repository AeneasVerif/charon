//@ known-failure
//@ charon-args=--opaque crate::Enum
enum Enum {
    A,
    B,
}

fn is_a(x: &Enum) -> bool {
    match x {
        Enum::A => true,
        Enum::B => false,
    }
}
