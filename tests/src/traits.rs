pub trait BoolTrait {
    fn get_bool(&self) -> bool;

    fn ret_true(&self) -> bool {
        true
    }
}

pub enum Option<T> {
    Some(T),
    None,
}

impl<T> BoolTrait for Option<T> {
    fn get_bool(&self) -> bool {
        match self {
            Option::Some(_) => true,
            Option::None => false,
        }
    }
}

pub fn test_bool_trait_option<T>(x: Option<T>) -> bool {
    x.get_bool() && x.ret_true()
}

pub fn test_bool_trait<T: BoolTrait>(x: T) -> bool {
    x.get_bool()
}

pub trait ToU64 {
    fn to_u64(self) -> u64;
}

impl ToU64 for u64 {
    fn to_u64(self) -> u64 {
        self
    }
}

impl<A: ToU64> ToU64 for (A, A) {
    fn to_u64(self) -> u64 {
        self.0.to_u64() + self.1.to_u64()
    }
}

pub fn f<T: ToU64>(x: (T, T)) -> u64 {
    x.to_u64()
}

fn g<T>(x: (T, T)) -> u64
where
    (T, T): ToU64,
{
    x.to_u64()
}

pub struct Wrapper<T> {
    x: T,
}

impl<T: ToU64> ToU64 for Wrapper<T> {
    fn to_u64(self) -> u64 {
        self.x.to_u64()
    }
}

pub fn h1(x: Wrapper<u64>) -> u64 {
    x.to_u64()
}

pub fn h2<T: ToU64>(x: Wrapper<T>) -> u64 {
    x.to_u64()
}

pub trait ToType<T> {
    fn to_type(self) -> T;
}

pub trait OfType {
    fn of_type<T: ToType<Self>>(x: T) -> Self
    where
        Self: std::marker::Sized;
}

pub fn h3<T1: OfType, T2: ToType<T1>>(y: T2) -> T1 {
    T1::of_type(y)
}
