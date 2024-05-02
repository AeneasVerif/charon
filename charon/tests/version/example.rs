//! Example file meant to exercise most of the variants of the llbc ast. This is used to detect
//! breaking changes to the llbc format.
#[derive(Copy, Clone)]
enum Foo {
    A(u32),
    B { field: bool },
}

type Bar = Foo;

trait Trait: Copy {
    type AssocType: Default;
    fn method() -> Self;
}

impl Trait for Foo {
    type AssocType = &'static str;
    fn method() -> Self {
        Foo::A(42)
    }
}

const CONST: isize = 128;

static STATIC: &'static bool = &false;

fn main() {
    let foo = <Foo as Trait>::method();
    match Some(foo) {
        Some(Foo::B { field: true }) => {}
        _ => panic!(),
    }
}
