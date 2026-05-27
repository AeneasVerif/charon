//@ charon-args=--targets=x86_64-unknown-linux-gnu,i686-unknown-linux-gnu
//@ charon-args=--hide-marker-traits
pub struct State<H> {
    _h: H,
}

pub fn caller<H>(h: H) {
    let _ = State { _h: h };
}
