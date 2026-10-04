//@ output=run-with-minirust
unsafe extern "Rust" {
    safe fn minirust_print(value: u32);
}

// FIXME(minirust): Constructing this char is UB, but MiniRust currently models char as u32 and
// accepts it.
fn invalid_char() -> char {
    unsafe { std::mem::transmute(0xD800u32) }
}

fn main() {
    minirust_print(invalid_char() as u32);
}
