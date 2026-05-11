//@ charon-args=--targets=x86_64-pc-windows-msvc,i686-unknown-linux-gnu
#[cfg(target_pointer_width = "64")]
pub struct Foo {
    pub x: u64,
}

#[cfg(target_pointer_width = "32")]
pub struct Foo {
    pub x: u32,
}

impl Foo {
    pub fn uses_const(&self) -> u32 {
        const TABLE: [u32; 4] = [10, 20, 30, 40];
        TABLE[0]
    }
}
