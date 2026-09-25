//@ no-default-options
//@ charon-args=--mir=elaborated --resugar-drops
struct NeedsDrop;
impl Drop for NeedsDrop {
    fn drop(&mut self) {}
}

fn consume<T>(_x: T) {}

pub fn conditional(x: NeedsDrop, move_x: bool) {
    if move_x {
        consume(x);
    }
}

fn pair1(pair: (NeedsDrop, NeedsDrop)) {
    if true {
        let _x = pair;
    } else {
        let (_x, _) = pair;
    }
}

fn pair2(pair: (NeedsDrop, NeedsDrop)) {
    match 42 {
        0 => {
            let _x = pair;
        }
        1 => {
            let (_x, _) = pair;
        }
        2 => {
            let (_, _x) = pair;
        }
        _ => {}
    }
}

pub fn pair3(pair: (NeedsDrop, NeedsDrop), move_pair: bool, move_first: bool) {
    if move_pair {
        let _x = pair;
        return;
    }
    if move_first {
        let (_x, _) = pair;
    }
}

pub fn re_assign(mut x: NeedsDrop) {
    if true {
        consume(x);
    }
    if true {
        x = NeedsDrop;
    }
}

pub fn in_loop(mut x: NeedsDrop) {
    while true {
        if true {
            consume(x);
        }
        x = NeedsDrop;
    }
}

enum EnumWithTwoDrops {
    Pair(NeedsDrop, NeedsDrop),
    Empty,
}

fn partial_enum_move(value: EnumWithTwoDrops, b: bool) {
    if b {
        consume(value);
    } else {
        match value {
            EnumWithTwoDrops::Pair(first, _) => consume(first),
            EnumWithTwoDrops::Empty => {}
        }
    }
}
