//@ known-failure

fn foo() -> impl Copy {
    foo
}

fn main() {
    foo();
}
