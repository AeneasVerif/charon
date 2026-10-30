//! A loop can't exit into an unwind path: these are translated inside the `on_unwind` block of
//! the statement that unwinds.
struct Guard;

impl Drop for Guard {
    fn drop(&mut self) {}
}

fn may_panic() {}

pub fn infinite_loop() {
    let _g = Guard;
    loop {
        may_panic()
    }
}
