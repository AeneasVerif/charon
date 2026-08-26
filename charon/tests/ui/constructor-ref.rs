enum Wrapper<T> {
    Value(T),
}

fn use_constructor<T, F: FnOnce(T) -> Wrapper<T>>(_: F) {}

fn constructor_ref<T>() {
    use_constructor::<T, _>(Wrapper::Value);
}
