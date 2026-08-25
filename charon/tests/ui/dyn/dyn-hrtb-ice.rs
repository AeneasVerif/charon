//@ known-failure

pub fn dyn_fn_arg<'a>(_: &dyn Fn(&'a i32)) {}

pub fn hrtb_fn_pointer(_: for<'a> fn(&'a dyn Fn(&'a u8))) {}

pub fn hrtb_dyn_fn(_: &dyn for<'a> Fn(&dyn Fn(&'a i32))) {}

pub trait Obj<'a> {
    type V;
}

pub fn f<'a>(_: &dyn Obj<'a, V = i32>) {}

fn main() {}
