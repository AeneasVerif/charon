fn call_test<'b, 'c : 'b, T>(f : &dyn for<'a> Fn(&'a bool) -> (T, bool, &'b T), arg: &'c bool) -> (T, bool, &'b T) {
    f(arg)
}

fn main() {
    let x = 2;
    let y = 3;
    call_test(&|a| (x, *a, &y), &false);
}