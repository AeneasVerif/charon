fn slice_pattern_end(x: &[()]) {
    match x {
        [.., _named] => (),
        _ => (),
    }
}

fn array_pattern_end(x: &[u32; 3]) -> u32 {
    let [.., last] = x;
    *last
}

struct Tail {
    prefix: u8,
    values: [u32],
}

fn field_pattern_end(x: &Tail) -> u32 {
    match x.values {
        [.., last] => last,
        _ => 0,
    }
}
