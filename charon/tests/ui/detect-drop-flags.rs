//@ no-default-options
//@ charon-args=--mir=elaborated --detect-drop-flags

struct NeedsDrop;

impl Drop for NeedsDrop {
    fn drop(&mut self) {}
}

fn consume<T>(_x: T) {}

pub fn conditional(x: NeedsDrop, move_x: bool) {
    if move_x {
        consume(x);
    }
}
