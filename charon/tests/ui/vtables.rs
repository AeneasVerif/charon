trait Super<T> {
    fn super_method(&self, arg: T) -> i32;
}
trait Checkable<T>: Super<T> {
    fn check(&self) -> bool;
}
impl Super<i32> for i32 {
    fn super_method(&self, arg: i32) -> i32 {
        *self + arg
    }
}
impl Checkable<i32> for i32 {
    fn check(&self) -> bool {
        self.super_method(10) > 0
    }
}
fn main() {
    let x : &dyn Checkable<i32> = &42;
    x.check();
}
