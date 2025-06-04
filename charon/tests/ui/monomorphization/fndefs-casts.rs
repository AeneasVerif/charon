//@ charon-args=--monomorphize
// Ensures casts of FnDefs monomorphise properly

fn foo<'a, T>(x: &'a T) {}

fn bar() {
    let fooint1: fn(&u8) = foo;
    let fooint2: fn(&u8) = foo;
    let foochar: fn(&char) = foo;

    let a = 11;
    fooint1(&a);
    let b = 12;
    fooint1(&a);
    fooint1(&b);
    fooint2(&b);

    foochar(&'x');
}
