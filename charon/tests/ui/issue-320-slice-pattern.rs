//@ known-failure

fn slice_pat() {
    let array: [_; 4] = [0; 4];
    let [_a, _b @ .., _c] = array;

    let array_ref: &[_; 4] = &[0; 4];
    let [_a, _b @ .., _c] = array_ref;

    let slice: &[_] = &[0; 4];
    let [_a, _b @ .., _c] = slice else { panic!() };
}
