//@ charon-args=--mir=elaborated
//@ charon-args=--add-drop-bounds
fn drop_array(_: [String; 4]) {}

fn drop_slice(_: Box<[String]>) {}

fn drop_tuple<A, B>(_: (A, B)) {}
