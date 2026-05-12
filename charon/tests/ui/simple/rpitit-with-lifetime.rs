trait Foo<T> {
    fn iter<'a>(&'a self) -> impl Iterator<Item = &'a T>
    where
        T: 'a;
}
