//@ output=run-with-minirust
// Constant pointers with projections and offsets into globals.
unsafe extern "Rust" {
    safe fn minirust_print(value: u32);
}

static ARR: [u32; 3] = [10, 20, 30];

fn main() {
    // One past the end: a typed in-bounds offset followed by a cast.
    let end = const { unsafe { (&raw const ARR).cast::<u32>().add(3) } };
    minirust_print(unsafe { *end.sub(1) });
}
