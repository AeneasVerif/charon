//@ charon-args=--monomorphize

trait Bound<'a> {}

impl<'a> Bound<'a> for () {}

fn callee<'a>()
where
    (): Bound<'a>,
{
}

fn caller<'a>()
where
    (): Bound<'a>,
{
    callee();
}

pub fn f() {
    caller()
}
