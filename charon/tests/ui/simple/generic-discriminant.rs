//@ charon-args=--include=core::mem::discriminant
pub fn f<T>(x: &T) -> std::mem::Discriminant<T> {
    std::mem::discriminant(x)
}
