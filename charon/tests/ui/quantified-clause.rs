fn foo<F>(_f: F)
where
    F: for<'a> FnMut(&'a ()),
{
}

fn bar<'b, T>()
where
    T: 'b,
    for<'a> &'b T: 'a,
{
}

// https://github.com/AeneasVerif/charon/issues/377
pub fn f<'a>(_: &'a ()) -> Option<(&'a u8,)> {
    None
}

pub trait Trait {}

// https://github.com/hacspec/hax/issues/747
impl<T, U> Trait for Result<T, U>
where
    for<'a> &'a Result<T, U>: IntoIterator,
    for<'a> <&'a Result<T, U> as IntoIterator>::Item: Copy,
{
}

pub trait Hrtb<T> {}

pub trait WithGat {
    type Gat<'a>: for<'b> Hrtb<(&'a (), &'b ())>;
}

pub struct S;
pub struct G;

impl<'a, 'b> Hrtb<(&'a (), &'b ())> for G {}

pub trait WithParent: for<'a> Hrtb<&'a ()> {}

impl<'a> Hrtb<&'a ()> for S {}
impl WithParent for S {}

impl WithGat for S {
    type Gat<'a> = G;
}
