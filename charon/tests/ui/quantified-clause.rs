fn foo<F>(_f: F)
where
    F: for<'a> FnMut(&'a ()),
{
}

fn bar<'b, T>()
where
    for<'a> &'b T: 'a,
{
}
