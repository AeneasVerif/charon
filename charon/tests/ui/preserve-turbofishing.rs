//@ revisions=promoted,elaborated
//@[elaborated] charon-args=--mir elaborated

pub fn foo<'a: 'a>(_: &'a u32) {}
pub fn bar<T>(_: T) {}

pub fn explicit_arguments(value: &'static u32) {
    foo::<'static>(value);
    bar::<&'static u32>(value);
    bar::<Option<&'static _>>(Some(value));
}

pub fn function_values(value: &'static u32) {
    let f = foo::<'static>;
    f(value);
    let f = bar::<&'static u32>;
    f(value);
    let f: fn(&'static u32) = bar::<&'static u32>;
    f(value);
}

pub fn named_arguments<'a, 'b>(value: &'a u32, other: &'b u32) {
    bar::<(&'a u32, _)>((value, other));
}

pub trait Project<'a> {
    type Output;
}

impl<'a, 'b: 'a> Project<'a> for &'b u32 {
    type Output = u32;
}

pub fn normalized_argument<'a, 'b: 'a>(value: u32) {
    bar::<<&'b u32 as Project<'a>>::Output>(value);
}

pub struct WithConst<T>(T);

impl<T> WithConst<T> {
    pub const NONE: Option<T> = None;

    pub fn consume<U>(_: T, _: U) {}
}

pub fn associated_items(value: &'static u32) {
    let x = WithConst::<&'static u32>::NONE;
    WithConst::<&'static u32>::consume::<&'static u32>(value, value);
}

pub trait Method {
    fn consume<T>(self, value: T);
}

impl Method for () {
    fn consume<T>(self, _: T) {}
}

pub fn trait_method(value: &'static u32) {
    ().consume::<&'static u32>(value);
}
