//@ known-failure

fn foo<F>(_f: F)
where
    F: for<'a> FnMut(&'a ()),
{
}
