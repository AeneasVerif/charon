//@ charon-args=--monomorphize
#![feature(trait_alias)]

trait A<T> {}

trait B = A::<i32>;

impl A<i32> for i32 {

}

fn f<T : B>() {

}

fn main() {
    f::<i32>();
}