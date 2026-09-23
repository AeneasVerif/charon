//@ revisions=default,silenced
//@[silenced] charon-arg=--opaque={impl core::marker::Destruct for crate::PortableHash}
//@ charon-args=--precise-drops
struct KeccakState;

struct PortableHash<const K: usize> {
    shake128_state: [KeccakState; K],
    make_non_trivial: Box<u32>,
}

fn foo(_: PortableHash<42>) {}
