pub struct WrapClone<T: Clone>(T);
pub fn wrap<U>() -> impl for<'a> FnOnce(&'a U) -> WrapClone<&'a U> {
    |x| WrapClone(x)
}
