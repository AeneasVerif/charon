//@ known-failure
//@ charon-args=--extract-opaque-bodies

fn vec(x: &mut Vec<u32>) {
    x.push(42)
}
