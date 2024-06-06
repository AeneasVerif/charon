#![feature(register_tool)]
#![register_tool(charon)]
#![register_tool(aeneas)]

#[charon::opaque]
pub trait BoolTrait {
    // Required method
    #[charon::opaque]
    fn get_bool(&self) -> bool;

    // Provided method
    #[charon::opaque]
    fn ret_true(&self) -> bool {
        true
    }
}

#[charon::opaque]
impl BoolTrait for bool {
    fn get_bool(&self) -> bool {
        *self
    }
}

#[charon::opaque]
pub fn test_bool_trait_option<T>(x: Option<T>) -> bool {
    x.get_bool() && x.ret_true()
}

#[charon::opaque]
type Test = i32;

#[charon::opaque]
const SIX_SIX_SIX: u32 = 600 + 60 + 6;

#[aeneas::opaque]
type Test2 = u32;
