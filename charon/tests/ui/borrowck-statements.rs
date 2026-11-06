//@ charon-args=--mir built

#![feature(impl_trait_in_bindings)]

pub enum Either<T> {
    Left(T),
    Right,
}

pub fn destructure<'a>(input: &'a Either<(u32, u64)>) -> &'a u32 {
    let Either::Left((x, _)): &Either<(u32, u64)> = input else {
        panic!()
    };
    x
}

pub fn index(xs: &[u32; 4], i: usize) -> u32 {
    xs[i]
}

pub trait UsesSelf: Sized {
    fn identity(value: Self) -> Self {
        let value: Self = value;
        value
    }
}

pub fn impl_trait_binding(value: u32) -> u32 {
    let value: impl Copy = value;
    value
}

pub fn nested_impl_trait(value: Box<u32>) {
    let value: Box<impl Copy> = value;
}

pub fn multiple_impl_traits(value: (u32, String)) {
    let value: (impl Copy, impl Clone) = value;
}

pub fn higher_ranked_impl_trait(value: for<'a> fn(&'a u32)) {
    let value: impl for<'a> Fn(&'a u32) = value;
}

pub fn impl_trait_outlives<'a, 'b>(value: &'a u32)
where
    'a: 'b,
{
    let value: impl Copy + 'b = value;
}

pub struct Foo<'a>(&'a u32);

impl Foo<'_> {
    pub fn set_type_self(self) {
        let x: Self = self;
    }
}

pub fn explicit_lifetimes<'a>(value: (&'static u32, &'a u32, &'a u32)) {
    let x: (&'static u32, &'a u32, &'a u32) = value;
}

pub struct StaticCopy<'a>(&'a u32);

impl Clone for StaticCopy<'static> {
    fn clone(&self) -> Self {
        *self
    }
}

impl Copy for StaticCopy<'static> {}

pub fn static_copy_bound<'a>(value: StaticCopy<'a>)
where
    'a: 'static,
{
    let x: impl Copy = value;
}

pub fn boxed_static_copy_bound<'a>(value: Box<StaticCopy<'a>>)
where
    'a: 'static,
{
    let x: Box<impl Copy> = value;
}

pub trait Project<'a> {
    type Output;
}

impl<'a, 'b: 'a> Project<'a> for &'b u32 {
    type Output = u32;
}

pub fn projection_outlives<'a, 'b>(value: u32)
where
    'b: 'a,
{
    let x: <&'b u32 as Project<'a>>::Output = value;
}
