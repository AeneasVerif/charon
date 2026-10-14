// Outlives relations mentioning a late-bound region belong on its binder.
pub fn function_pointer<T>(_: for<'a> fn(&'a T)) {}

pub fn nested_function_pointer<T>(_: for<'a> fn(for<'b> fn(&'b T), &'a T)) {}

pub fn outermost_binder<T>(_: for<'a> fn(for<'b> fn(&'a T))) {}

pub fn region_outlives<'b, T>(_: for<'a> fn(&'a &'b T)) {}

pub fn reference_to_function_pointer<'a>(_: &'a for<'b> fn(&'b u32)) {}

pub fn reference_with_outer_region<'a, 'c>(_: &'a for<'b> fn(&'c u32)) {}
