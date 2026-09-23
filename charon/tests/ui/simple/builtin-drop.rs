//@ revisions=poly,mono
//@[mono] charon-args=--monomorphize
//@[mono] charon-args=--include=core::marker::Destruct
//@ charon-args=--precise-drops
fn drop_array(_: [String; 4]) {}

fn drop_slice(_: Box<[String]>) {}

fn drop_tuple<A, B>(_: (A, B)) {}

fn drop_tuple_string(_: (String, String)) {}
