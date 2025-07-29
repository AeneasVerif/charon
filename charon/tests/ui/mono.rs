trait Modifiable<T> {
    fn modify(&mut self, arg: &T) -> T;
}
impl <T : Clone> Modifiable<T> for i32 {
    fn modify(&mut self, arg: &T) -> T {
        *self += 1;
        arg.clone()
    }
}
fn modify_something<T: Clone>(arg: &T) -> T {
    let x = &mut 199;
    x.modify(arg)
}
fn main() {
    let y = &mut 99;
    assert!(!modify_something(&"Hello, world!".to_string()).is_empty());
    assert_eq!(y.modify(&mut 100), 100);
}
