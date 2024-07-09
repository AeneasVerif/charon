trait Foo<'a>: Copy {
    // FIXME: the `+ 'a` appears to be completely ignored.
    type Item: Clone + 'a;

    fn use_item(x: &Self::Item) -> &Self::Item {
        x
    }
}

impl<'a, T> Foo<'a> for &'a T {
    type Item = Option<&'a T>;
}

fn external_use_item<'a, T: Foo<'a>>(x: T::Item) -> T::Item {
    x.clone()
}

fn call_fn() {
    let _ = external_use_item::<&bool>(None);
}

fn type_equality<'a, I, J>(x: I::Item) -> J::Item
where
    I: Foo<'a>,
    J: Foo<'a, Item = I::Item>,
{
    x
}
