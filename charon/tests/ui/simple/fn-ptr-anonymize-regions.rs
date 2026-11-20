struct NeedsFn<F: FnOnce(A), A>(F, A);

fn simple(
    _: NeedsFn<for<'a> fn(&'a u8), &'static u8>,
    _: NeedsFn<for<'b> fn(&'b u8), &'static u8>,
) {
}
