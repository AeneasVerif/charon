//@ charon-args=--lift-associated-types=*

trait Ring {
    type Sub: Field;
    const ZERO: Self;
}

trait Field: Ring {
    type Packing;
}

fn zero<R: Ring>() {
    let _ = R::Sub::ZERO;
}
