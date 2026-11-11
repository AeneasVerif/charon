//@ known-failure
//@ rustc-args=-Znext-solver=coherence -Zno-leak-check
//@ charon-args=--no-borrow-check
// From nll/relate_tys/impl-fn-ignore-binder-via-bottom.rs.

trait Factory {
    type Function;
    fn make() -> Self::Function;
}

impl<T> Factory for fn(T) {
    type Function = fn(T);

    fn make() -> Self::Function {
        |_| {}
    }
}

fn higher_ranked_impl() {
    let _function = <fn(&())>::make();
}
