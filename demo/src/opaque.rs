pub struct S {
    x: i32, /* private field */
}

pub fn create(x: i32) -> S {
    S { x }
}

pub fn get_field<'a>(s: &'a mut S) -> &'a mut i32 {
    &mut s.x
}
