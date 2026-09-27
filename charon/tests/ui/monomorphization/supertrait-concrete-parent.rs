//@ charon-args=--monomorphize

pub trait Buf: AsRef<str> {}

pub struct EngineStr(String);

impl AsRef<str> for EngineStr {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl Buf for EngineStr {}
