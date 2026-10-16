//@charon-args=--consts=values
// Pointers to and into other globals must keep pointing to the same place.
struct Sync<T>(T);
unsafe impl<T> std::marker::Sync for Sync<T> {}

static ARR: [u32; 3] = [1, 2, 3];
static SECOND: &u32 = &ARR[1];
static SUFFIX: &[u32] = ARR.split_at(1).1;
// Offsets: one past the end, by one byte, and outside of the allocation.
static END: Sync<*const u32> = Sync(unsafe { (&raw const ARR).cast::<u32>().add(3) });
static BYTE: Sync<*const u8> = Sync(unsafe { (&raw const ARR).cast::<u8>().add(5) });
static BEFORE: Sync<*const u32> = Sync((&raw const ARR).cast::<u32>().wrapping_sub(1));

enum E {
    A(u8),
    B(u16, u32),
}
static E0: E = E::B(4, 5);
static E0_FIELD: &u32 = match &E0 {
    E::B(_, x) => x,
    E::A(..) => &0,
};

// Into an anonymous allocation.
static ANON: &(u32, u32) = &(1, 2);
static ANON_SECOND: &u32 = &ANON.1;
// Into an anonymous allocation, at an unsized type.
trait Trait: std::marker::Sync {}
impl Trait for u8 {}
static ANON_DYN: &dyn Trait = &(&(42u8, 12u8)).1;

// Into a function.
fn foo() {}
static FN_PTR: Sync<*const ()> = Sync(foo as fn() as *const ());
static FN_OFFSET: Sync<*const u8> = Sync((foo as fn() as *const u8).wrapping_add(1));

fn main() {}
