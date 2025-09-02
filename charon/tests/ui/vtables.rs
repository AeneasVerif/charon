#![feature(trait_alias)]
trait Super<T> {
    type Output;
    fn super_method(&self, arg: T) -> Self::Output;
}
trait Checkable<T>: Super<T> {
    fn check(&self) -> bool;
}
impl Super<i32> for i32 {
    type Output = i32;
    fn super_method(&self, arg: i32) -> i32 {
        *self + arg
    }
}
impl Checkable<i32> for i32 {
    fn check(&self) -> bool {
        self.super_method(10) > 0
    }
}
fn use_checkable(x: &dyn Checkable<i32, Output = i32>) -> bool {
    x.check()
}
impl Super<i32> for String {
    type Output = i32;
    fn super_method(&self, arg: i32) -> i32 {
        self.len() as i32 + arg
    }
}
impl Checkable<i32> for String {
    fn check(&self) -> bool {
        self.super_method(0) >= 0
    }
}

impl<const N: usize> Super<i32> for [String; N] {
    type Output = i32;
    fn super_method(&self, arg: i32) -> i32 {
        if N > 0 { arg + self[0].len() as i32 } else { arg }
    }
}
impl<const N: usize> Checkable<i32> for [String; N] {
    fn check(&self) -> bool {
        self.super_method(0) >= 0
    }
}

impl Super<i32> for (i32, String) {
    type Output = i32;
    fn super_method(&self, arg: i32) -> i32 {
        self.0 + self.1.len() as i32 + arg
    }
}
impl Checkable<i32> for (i32, String) {
    fn check(&self) -> bool {
        self.super_method(0) > 0
    }
}

fn extra_checks() {
    let b : String = String::from("Hello");
    assert!(use_checkable(&b as &dyn Checkable<i32, Output = i32>));

    let arr = [String::from("test"), String::from("array")];
    assert!(use_checkable(&arr as &dyn Checkable<i32, Output = i32>));

    let tup = (10, String::from("tuple"));
    assert!(use_checkable(&tup as &dyn Checkable<i32, Output = i32>));
}

trait NoParam {
    fn dummy(&self);
}
impl NoParam for i32 {
    fn dummy(&self) {
        assert!(*self > 0);
    }
}
impl NoParam for Box<i64> {
    fn dummy(&self) {
        assert!(**self > 0);
    }
}
// These should have empty {drop_method} bodies
impl NoParam for (i32, i32) {
    fn dummy(&self) {
        assert!(self.0 > self.1);
    }
}
impl NoParam for [i32; 10] {
    fn dummy(&self) {
        assert!(self[0] < self[9]);
    }
}
impl <const N: usize, const M: usize> NoParam for
    [(String, [(i32, i32); M], [(i32, String); M]); N] {
    fn dummy(&self) { }
}
fn composite_no_param() {
    let x: &dyn NoParam = &(42, 21);
    x.dummy();
    let y: &dyn NoParam = &[1,2,3,4,5,6,7,8,9,10];
    y.dummy();
    let complex: &dyn NoParam =
        &[(String::from("hello"), [(1, 2); 2], [(9, String::from("world")), (0, String::from("!"))]); 1];
    complex.dummy();
}
fn to_dyn_obj<T: NoParam>(arg: &T) -> &dyn NoParam {
    arg
}

trait Modifiable<T> {
    fn modify(&mut self, arg: &T) -> T;
}
impl<T: Clone> Modifiable<T> for i32 {
    fn modify(&mut self, arg: &T) -> T {
        *self += 1;
        arg.clone()
    }
}
fn modify_trait_object<T: Clone>(arg: &T) -> T {
    let x: &mut dyn Modifiable<T> = &mut 199;
    x.modify(arg)
}

trait BaseOn<T> {
    fn operate_on(&self, t: &T);
}
trait Both32And64: BaseOn<i32> + BaseOn<i64> {
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
impl Both32And64 for i32 {}
trait Alias = Both32And64;

trait LifetimeTrait {
    type Ty;
    fn lifetime_method<'a>(&self, arg: &'a Self::Ty) -> &'a Self::Ty;
}
impl LifetimeTrait for i32 {
    type Ty = i32;
    fn lifetime_method<'a>(&self, arg: &'a Self::Ty) -> &'a Self::Ty {
        assert!(*self > *arg);
        arg
    }
}
fn use_lifetime_trait<'a>(x: &dyn LifetimeTrait<Ty = i32>, y: &'a i32) -> &'a i32 {
    x.lifetime_method(y)
}

fn use_alias(x: &dyn Alias) {
    x.both_operate(&100, &200);
}



fn main() {
    let x: &dyn Checkable<i32, Output = i32> = &42;
    assert!(x.check());
    let y: &mut dyn Modifiable<i32> = &mut 99;
    assert!(!modify_trait_object(&"Hello".to_string()).is_empty());
    assert_eq!(y.modify(&mut 100), 100);
    let z: &dyn NoParam = to_dyn_obj(&42);
    z.dummy();
    let b : &dyn NoParam = &Box::new(64i64);
    b.dummy();
    let a: &dyn Both32And64 = &42;
    a.both_operate(&100, &200);
    let b: &dyn LifetimeTrait<Ty = i32> = &42;
    assert_eq!(*use_lifetime_trait(b, &10), 10);
}
