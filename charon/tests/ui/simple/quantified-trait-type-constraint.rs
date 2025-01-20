trait Trait<'a> {
    type Type;
}

fn foo<T>()
where
    T: for<'a> Trait<'a, Type = &'a ()>,
{
}
