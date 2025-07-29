#![feature(trait_alias)]
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
trait BaseOn<T> {
    fn operate_on(&self, t : &T);
}
trait Both32And64 : BaseOn<i32> + BaseOn<i64> {
    fn both_operate(&self, t32: &i32, t64: &i64) {
        self.operate_on(t32);
        self.operate_on(t64);
    }
}
impl BaseOn<i32> for i32 {
    fn operate_on(&self, t: &i32) {
        assert!(*self > *t);
    }
}
impl BaseOn<i64> for i32 {
    fn operate_on(&self, t: &i64) {
        assert!(*self as i64 > *t);
    }
}
impl Both32And64 for i32 { }
trait Alias = Both32And64;
fn use_alias(x: &dyn Alias) {
    x.both_operate(&100, &200);
}
trait Internal {
    type IntAssoc;
    fn internal_method(&self) -> Self::IntAssoc;
}
trait Left : Internal {
    type LeftAssoc;
    fn left_method(&self) -> Self::LeftAssoc;
}
trait Right<T> : Internal + Super<T> {
    type RightAssoc;
    fn right_method(&self) -> Self::RightAssoc;
}
trait Join<T> : Left + Right<T> {
    fn join_method(&self) -> (Self::LeftAssoc, Self::RightAssoc);
}
impl Internal for i32 {
    type IntAssoc = i32;
    fn internal_method(&self) -> Self::IntAssoc {
        *self + 1
    }
}
impl Left for i32 {
    type LeftAssoc = i32;
    fn left_method(&self) -> Self::LeftAssoc {
        *self + 2
    }
}
impl Right<i32> for i32 {
    type RightAssoc = i32;
    fn right_method(&self) -> Self::RightAssoc {
        *self + 3 + self.internal_method() + self.super_method(10)
    }
}
impl Join<i32> for i32 {
    fn join_method(&self) -> (Self::LeftAssoc, Self::RightAssoc) {
        (self.left_method(), self.right_method())
    }
}
fn main() {
    let x : &dyn Checkable<i32> = &42;
    assert!(x.check());
    let y : &mut dyn Modifiable<i32> = &mut 99;
    assert!(!modify_trait_object(&"Hello".to_string()).is_empty());
    assert_eq!(y.modify(&mut 100), 100);
    let z : &dyn NoParam = to_dyn_obj(&42);
    z.dummy();
    let a : &dyn Both32And64 = &42;
    a.both_operate(&100, &200);
    let b : &dyn Alias = &42;
    use_alias(b);
    let c : &dyn Join<i32, Internal=i32, Left=i32, Right=i32> = &97;
    let (left, right) = c.join_method();
    assert_eq!(left, 99);
    assert_eq!(right, 100);
}
