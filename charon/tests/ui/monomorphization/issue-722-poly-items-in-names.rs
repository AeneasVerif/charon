//@ charon-args=--monomorphize --start-from=crate::main

// Regression test for https://github.com/AeneasVerif/charon/issues/722.
trait SomeTrait {
    fn some_method(&self);
}

struct Point<T> {
    x: i32,
    y: u64,
    z: T,
}

impl SomeTrait for Point<i32> {
    fn some_method(&self) {
        assert!(self.x > 0 && self.y < 100 && self.z != 0);
    }
}

fn main() {
    let p = Point { x: 10, y: 50, z: 1 };
    p.some_method();
}
