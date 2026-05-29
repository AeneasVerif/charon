// Regression test for https://github.com/AeneasVerif/charon/issues/792.
trait Internal {
    type IntAssoc;

    fn internal_method(&self) -> Self::IntAssoc;
}

impl Internal for i32 {
    type IntAssoc = i32;

    fn internal_method(&self) -> Self::IntAssoc {
        *self + 1
    }
}

fn main() {}
