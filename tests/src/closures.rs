/*pub fn incr_u32(x: u32) -> u32 {
    x + 1
}

/*
/* Testing function pointers and closures */
// TODO: this requires to take into account the constraints over associated types
// because the output type of the Fn trait is an associated type, not a parameter.
// More precisely, we have the constraint that:
// <F as Fn<T>>::Output = T
#[allow(clippy::manual_map)]
pub fn map_option<T, F>(x: Option<T>, f: F) -> Option<T>
where
    F: Fn(T) -> T,
{
    match x {
        None => None,
        Some(x) => Some(f(x)),
    }
}
*/

// With a pointer to a top level function
pub fn test_map_option1(x: Option<u32>) -> Option<u32> {
    map_option(x, incr_u32)
}
*/

/*
//
pub fn test_closure1<T>(x: &T) -> &T {
    //let f: fn(&T) -> &T = |x| x;
    let f: fn(u32) -> u32 = |x| x;
    //(f)(x)
    x
}
*/

/*
// With a local function
pub fn test_map_option2(x: Option<u32>) -> Option<u32> {
    let f: fn(u32) -> u32 = |x| x + 1;
    map_option(x, f)
}

/*
// With a local function which uses local type variables
pub fn test_map_option3<T, U>(_: T, x: Option<U>) -> Option<U> {
    let f: fn(U) -> U = |x| x;
    map_option(x, f)
}
*/

/*// With a `dyn`
pub fn test_map_option3(x: Option<u32>) -> Option<u32> {
    let f: fn(u32) -> u32 = |x| x + 1;
    map_option(x, f)
}*/

/*

pub fn map(x: [i32; 256]) -> [i32; 256] {
    x.map(|v| v)
}

*/
*/

/*
macro_rules! impl_generic_struct {
    ($name:ident) => {
        pub struct $name<const SIZE: usize> {
            pub value: [u8; SIZE],
        }

        impl<const SIZE: usize> TryFrom<&[u8]> for $name<SIZE> {
            type Error = core::array::TryFromSliceError;

            fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
                match value.try_into() {
                    Ok(value) => Ok(Self { value }),
                    Err(e) => Err(e),
                }
            }
        }
    };
}

impl_generic_struct!(KyberCiphertext);
*/

/*
use std::convert::{TryFrom, TryInto};

pub struct KyberCypherText<const SIZE: usize> {
    pub value: [u8; SIZE],
}

impl<const SIZE: usize> TryFrom<&[u8]> for KyberCypherText<SIZE> {
    type Error = core::array::TryFromSliceError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        match value.try_into() {
            Ok(value) => Ok(Self { value }),
            Err(e) => Err(e),
        }
    }
}
*/
