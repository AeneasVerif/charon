#![feature(trait_alias)]

/// Local and foreign crates are translated at different MIR levels: the latter have elaborated
/// drops.
pub fn unbox(b: Box<u32>) -> u32 {
    *b
}

/// The message is a promoted constant, local to every crate that translates this body.
pub fn check(n: u32) -> u32 {
    assert!(n > 0, "n is zero");
    n
}

/// In a module so that it is the last trait of this crate's translation: trait aliases have no
/// associated item names.
pub mod m {
    pub trait Alias = Clone;
}
