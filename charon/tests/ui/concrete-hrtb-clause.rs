//! A higher-ranked where-clause on a concrete type is picked by rustc over the impl. The trait
//! proofs of a concrete item reference must therefore not be shared between items.
pub trait Tr {
    const C: u32;
}
impl<'a> Tr for &'a u32 {
    const C: u32 = 1;
}
pub struct W<T: Tr>(pub T);

pub fn with_clause() -> u32
where
    for<'a> &'a u32: Tr,
{
    let _x: Option<W<&'static u32>> = None;
    <&'static u32 as Tr>::C
}

pub fn without_clause() -> u32 {
    let _x: Option<W<&'static u32>> = None;
    <&'static u32 as Tr>::C
}

fn main() {}
