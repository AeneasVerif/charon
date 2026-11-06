//@ charon-args=--print-layouts --monomorphic-layouts

struct Wrap<T>(Option<T>);
struct Grow<T>(T, *const Grow<(T, T)>);
struct Ref<'a>(&'a u8);
struct Holder<'a>(Wrap<&'a u16>);
fn instances(_: Wrap<bool>, _: (u8, &u32), _: Grow<u8>, _: Ref<'_>, _: Holder<'_>) {}
fn generic<T>(_: Option<T>) {}
fn opaque() -> impl Copy {
    0u8
}
fn uses_opaque() {
    let _ = Some(opaque());
}
