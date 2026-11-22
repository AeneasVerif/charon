//@ charon-args=--consts=values --monomorphize
// A constant pointing to an allocation, evaluated in items with different typing environments.
const TABLE: &[u8; 3] = &[1, 2, 3];

fn generic<T>() -> &'static [u8; 3] {
    const { TABLE }
}

pub fn use_generic() {
    let _ = generic::<u8>();
    let _ = generic::<u32>();
    let _ = TABLE;
}
