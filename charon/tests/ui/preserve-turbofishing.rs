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

pub struct Record<'a, T: Copy> {
    pub borrowed: &'a u32,
    pub value: T,
}

pub enum Choice<T> {
    Item { value: T },
}

pub union Union<'a> {
    pub value: &'a u32,
}

pub fn explicit_aggregates(value: &'static u32) {
    let record = Record::<'static, &'static u32> {
        borrowed: value,
        value,
    };
    let choice = Choice::<&'static u32>::Item { value };
    let union = Union::<'static> { value };
    let tuple = WithConst::<&'static u32>(value);
}

pub fn named_aggregate<'a, 'b>(value: &'a u32, other: &'b u32) {
    // Infer the second argument while preserving the explicit lifetime.
    let record = Record::<'a, _> {
        borrowed: value,
        value: other,
    };
    let updated = Record::<'a, _> {
        borrowed: value,
        ..record
    };
}

pub fn normalized_aggregate<'a, 'b: 'a>(borrowed: &'a u32, value: u32) {
    // Normalizing the argument must also preserve the constraint `'b: 'a`.
    let record = Record::<'a, <&'b u32 as Project<'a>>::Output> { borrowed, value };
}
