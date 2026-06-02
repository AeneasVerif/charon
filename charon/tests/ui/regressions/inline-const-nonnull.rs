//@ known-failure

fn main() {
    const { std::ptr::NonNull::<u8>::dangling() };
}
