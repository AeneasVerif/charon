//@ charon-args=--targets=x86_64-pc-windows-msvc,aarch64-pc-windows-msvc

pub trait WithAssocConstDefault {
    const N: usize = 4;
}

pub trait WithAssocConstNoDefault {
    const N: usize;
}

pub struct S;
impl WithAssocConstNoDefault for S {
    const N: usize = 7;
}
