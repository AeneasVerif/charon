//@ charon-args=--mir optimized
fn into_inner(b: Box<String>) -> String {
    *b
}

fn write(mut b: Box<String>, s: String) {
    *b = s;
}

fn borrow(mut b: Box<String>) {
    let _ = &mut *b;
}

fn reborrow(b: &mut Box<String>) -> &mut String {
    &mut *b
}

struct Struct {
    a: i32,
    b: String,
}

fn field(b: Box<Struct>) -> String {
    b.b
}
