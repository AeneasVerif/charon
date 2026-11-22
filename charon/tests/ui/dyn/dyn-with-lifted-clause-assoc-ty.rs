//@ charon-args=--lift-associated-types=*
pub trait Input {
    type Span;
}

pub trait Parser<I: Input> {
    fn parse(&self, input: I);
}

pub fn use_dyn<I: Input>(p: &dyn Parser<I>, input: I) {
    p.parse(input)
}
