//@ no-default-options
//@ charon-args=--precise-drops --desugar-drops

trait T {}

struct A(dyn T);

fn f(_: Box<A>) {}
