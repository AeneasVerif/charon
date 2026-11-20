//@ charon-args=--monomorphize --hide-marker-traits
pub trait Tr {}
impl Tr for u32 {}
pub struct S(Box<u8>)
where
    u32: Tr;
pub fn drop_s(_: S) {}
pub fn closure() -> impl FnOnce()
where
    u32: Tr,
{
    || ()
}
pub fn use_closure() {
    closure()()
}
