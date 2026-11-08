//@ revisions=current,next
//@ charon-args=--mir promoted
//@[current] rustc-args=-Znext-solver=coherence
//@[next] rustc-args=-Znext-solver=globally
#![feature(type_alias_impl_trait)]
// Type annotations can contain opaques, which used to cause an ICE in our annotation recovery
// logic.

pub fn destructure<'a>(x: &'a u32) -> &'a u32 {
    type Pair<'a> = impl Sized + 'a;
    let (x, _): Pair<'a> = (x, 0u32);
    x
}

type Opaque = impl Sized;

#[define_opaque(Opaque)]
fn define() -> Opaque {
    0u32
}

pub fn construct() {
    let _ = None::<Opaque>;
}
