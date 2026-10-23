//@ charon-args=--hide-marker-traits --precise-drops

pub struct ArrayAndSlice<'a, T> {
    pub array: [T; 2],
    pub slice: &'a [T],
}
