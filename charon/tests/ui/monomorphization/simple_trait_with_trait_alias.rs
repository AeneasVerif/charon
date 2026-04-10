//@ charon-args=--monomorphize
#![feature(trait_alias)]

trait A {}

trait B = A;

impl A for i32 {

}

fn f<T : B>() {

}

fn main() {
    f::<i32>();
}
