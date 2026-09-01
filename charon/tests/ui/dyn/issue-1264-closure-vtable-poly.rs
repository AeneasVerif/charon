//@ charon-args=--include=core::ops::function

struct Droppable(u32);
impl Drop for Droppable {
    fn drop(&mut self) {}
}

// The vtable instance for a closure capturing a generic is itself generic.
fn wrap<T: 'static>(x: T) -> Box<dyn FnOnce() -> T> {
    Box::new(move || x)
}

fn main() {
    let f: &dyn Fn(u32) -> u32 = &|x| x + 1;
    let _y = f(1);
    // A closure with captured state.
    let captured = 10;
    let g: &dyn Fn(u32) -> u32 = &|x| x + captured;
    let _y = g(2);
    // Built but not called: the drop shim must drop the captured state.
    let d = Droppable(0);
    let _h: Box<dyn FnOnce() -> Droppable> = Box::new(move || d);
    let _w = wrap(3u32);
}
