trait Ord {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering;
}

fn use_fn<T, F: FnOnce(&T, &T) -> std::cmp::Ordering>(_: F) {}

fn method_ref<T: Ord>() {
    let _ = T::cmp;
    use_fn::<T, _>(T::cmp);
}
