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
trait Modifiable<T> {
    fn modify(&mut self, arg: &T) -> T;
}
impl <T : Clone> Modifiable<T> for i32 {
    fn modify(&mut self, arg: &T) -> T {
        *self += 1;
        arg.clone()
    }
}
trait NoParam {
    fn dummy(&self);
}
impl NoParam for i32 {
    fn dummy(&self) {
        assert!(*self > 0);
    }
}
fn to_dyn_obj<T: NoParam>(arg: &T) -> &dyn NoParam {
    arg
}
fn modify_trait_object<T : Clone>(arg: &T) -> T {
    let x : &mut dyn Modifiable<T> = &mut 199;
    x.modify(arg)
}
fn main() {
    let x : &dyn Checkable<i32> = &42;
    assert!(x.check());
    let y : &mut dyn Modifiable<i32> = &mut 99;
    assert!(!modify_trait_object(&"Hello".to_string()).is_empty());
    assert_eq!(y.modify(&mut 100), 100);
}
