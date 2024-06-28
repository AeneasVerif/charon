//@ known-failure
trait Foo {
    type Item;
}
trait ArraySize {
    type ArrayType<T>: Foo<Item = T>;
}
