//@ charon-args=--monomorphize
//! `Wrapper<dyn Sub>` is mentioned in two items whose generic parameter counts differ. The
//! `dyn Sub` type must come out the same in both, otherwise `Wrapper<dyn Sub>` is declared twice.
//! The unused type parameter of `generic_context` is what makes the counts differ; it is the
//! point of the test.

trait Sub {}
struct D;
impl Sub for D {}

struct Wrapper<T: ?Sized>(*const T);

fn generic_context1<T>(_: Wrapper<dyn Sub>) {}
fn generic_context2<T, U>(_: Wrapper<dyn Sub>) {}
fn generic_context3<T, U, V>(_: Wrapper<dyn Sub>) {}

fn main() {
    let d = D;
    generic_context1::<u8>(Wrapper(&d as *const dyn Sub));
    generic_context2::<u8, u8>(Wrapper(&d as *const dyn Sub));
    generic_context3::<u8, u8, u8>(Wrapper(&d as *const dyn Sub));
}
