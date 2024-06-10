#![feature(register_tool)]
#![register_tool(charon)]
#![register_tool(aeneas)]

#[charon::rename(BoolTest)]
pub trait BoolTrait {
    // Required method
    #[charon::rename(getTest)]
    fn get_bool(&self) -> bool;

    // Provided method
    #[charon::rename(retTest)]
    fn ret_true(&self) -> bool {
        true
    }
}

#[charon::rename(BoolImpl)]
impl BoolTrait for bool {
    fn get_bool(&self) -> bool {
        *self
    }
}

#[charon::rename(BoolFn)]
pub fn test_bool_trait<T>(x: bool) -> bool {
    x.get_bool() && x.ret_true()
}

#[charon::rename(TypeTest)]
type Test = i32;

#[charon::rename(VariantsTest)]
enum SimpleEnum {
    FirstVariant,
    SecondVariant,
    ThirdVariant,
}

#[charon::rename(FieldTest)]
pub struct IdType<T>(T);

#[aeneas::rename(TypeAeneas)]
type Test2 = u32;



