pub trait Supertrait {
    fn super_method(&self) -> u32;
}
pub trait Subtrait: Supertrait {}

pub fn call_super(obj: &dyn Subtrait) -> u32 {
    obj.super_method()
}
