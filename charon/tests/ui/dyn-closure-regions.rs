//@ known-failure
fn call_test<'b, 'c : 'b, T>(f : &dyn for<'a> Fn(&'a bool) -> (T, bool, &'b T), arg: &'c bool) -> (T, bool, &'b T) {
    f(arg)
}

fn main() {
    let x = 2;
    let y = 3;
    call_test(&|a| (x, *a, &y), &false);
}

// To generate region binders for this example,
// 1. initially, generics.regions contains captured variables `x` and `y`,
//      as <'_Bound(0, 0), '_Bound(0, 1)>;
// 2. for the late-bound region binders, we have `'a`, as a bound_var (push);
// 3. At last, we need the region for the receiver as the head first binder (insert_and_shift_ids).
// As a result, the generics.regions looks like `<Erased, '_Bound(0, 0), '_Bound(0, 1), Erased>`.