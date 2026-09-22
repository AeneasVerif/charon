//@ known-failure

const fn opaque() -> impl Sized {}

fn main() {
    const { opaque() };
}
