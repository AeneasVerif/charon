//@ output=run-with-minirust
use std::num::NonZeroU32;

unsafe extern "Rust" {
    safe fn minirust_print(value: u32);
}

// Evil
fn write_zero(x: &mut NonZeroU32) {
    unsafe { std::ptr::from_mut(x).cast::<u32>().write(0) };
}

fn main() {
    let mut option = NonZeroU32::new(1);
    match &mut option {
        Some(nonzero) => write_zero(nonzero),
        None => unreachable!(),
    }
    // Could (should?) be UB to read `None`
    match option {
        Some(_) => minirust_print(1),
        None => minirust_print(0),
    }
}
