//@ output=pretty-llbc
enum Ordering {
    Lesser = -1,
    Equal = 0,
    Greater = 1,
}

fn main() {
    match Ordering::Lesser {
        Ordering::Lesser => {}
        _ => {}
    }
}
