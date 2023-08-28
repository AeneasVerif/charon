pub trait BoolTrait {
    // Declared method
    fn get_bool(&self) -> bool;

    // Provided methods
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

pub fn g<T>(x: (T, T)) -> u64
where
    (T, T): ToU64,
{
    x.to_u64()
}

pub fn h0(x: u64) -> u64 {
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

impl ToType<bool> for u64 {
    fn to_type(self) -> bool {
        self > 0
    }
}

pub trait OfType {
    fn of_type<T: ToType<Self>>(x: T) -> Self
    where
        Self: std::marker::Sized;
}

pub fn h3<T1: OfType, T2: ToType<T1>>(y: T2) -> T1 {
    T1::of_type(y)
}

// Checking what happens if we move trait clauses from a method to its enclosing block
pub trait OfTypeBis<T: ToType<Self>>
where
    Self: std::marker::Sized,
{
    fn of_type(x: T) -> Self
    where
        Self: std::marker::Sized;
}

pub fn h4<T1: OfTypeBis<T2>, T2: ToType<T1>>(y: T2) -> T1 {
    T1::of_type(y)
}

pub struct TestType<T>(T);

// Checking what happens with nested blocks
impl<T: ToU64> TestType<T> {
    pub fn test(&self, x: T) -> bool {
        struct TestType1(u64);
        trait TestTrait {
            fn test(&self) -> bool;
        }

        // Remark: we can't write: impl TestTrait for TestType<T>,
        // we have to use a *local* parameter (can't use the outer T).
        // In other words: the parameters used in the items inside
        // an impl must be bound by the impl block (can't come from outer
        // blocks).

        impl TestTrait for TestType1 {
            fn test(&self) -> bool {
                self.0 > 1
            }
        }

        let x = x.to_u64();
        let y = TestType1(0);
        x > 0 && y.test()
    }
}

pub struct BoolWrapper(pub bool);

impl<T> ToType<T> for BoolWrapper
where
    bool: ToType<T>,
{
    fn to_type(self) -> T {
        self.0.to_type()
    }
}

pub trait WithConstTy<const LEN: usize> {
    const LEN1: usize;
    // Testing default values
    const LEN2: usize = 32;

    type V;
    type W: ToU64;

    // Below: we can't use [Self::Len1] in the type of the array.
    // Probably because of dyn traits...
    fn f(x: &mut Self::W, y: &[u8; LEN]);
}

impl WithConstTy<32> for bool {
    const LEN1: usize = 12;

    type V = u8;
    type W = u64;

    fn f(_: &mut Self::W, _: &[u8; 32]) {}
}

pub fn use_with_const_ty1<const LEN: usize, H: WithConstTy<LEN>>() -> usize {
    H::LEN1
}

pub fn use_with_const_ty2<const LEN: usize, H: WithConstTy<LEN>>(_: H::W) {}

pub fn use_with_const_ty3<const LEN: usize, H: WithConstTy<LEN>>(x: H::W) -> u64 {
    x.to_u64()
}

pub fn test_where1<'a, T: 'a>(_x: &'a T) {}
pub fn test_where2<T: WithConstTy<32, V = u32>>(_x: T::V) {}

// Below: testing super traits.
//
// Actually, this comes for free: ChildTrait : ParentTrait just adds a trait
// clause for Self: `Self : ParentTrait`.
pub trait ParentTrait1 {}
pub trait ParentTrait2 {}
pub trait ChildTrait: ParentTrait1 + ParentTrait2 {}

// TODO: where clauses
// TODO: super traits
