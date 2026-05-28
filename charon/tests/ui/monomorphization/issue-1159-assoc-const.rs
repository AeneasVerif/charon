//@ charon-args=--monomorphize --start-from-pub
//@ known-failure
pub trait MyConfig {
    const SLICE_HOLDER: Option<&'static [u64]>;
    fn op(x: u64) -> u64;
}

pub struct Concrete;

impl MyConfig for Concrete {
    const SLICE_HOLDER: Option<&'static [u64]> = {
        const ARR: [u64; 1] = [7u64];
        Some(&ARR)
    };

    fn op(x: u64) -> u64 {
        x + 1
    }
}

pub fn entry(x: u64) -> u64 {
    <Concrete as MyConfig>::op(x)
}
