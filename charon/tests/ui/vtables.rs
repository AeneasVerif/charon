trait Checkable {
    fn check(&self) -> bool;
}
impl Checkable for i32 {
    fn check(&self) -> bool {
        *self > 0
    }
}
fn main() {
    let x : &dyn Checkable = &42;
    x.check();
}
