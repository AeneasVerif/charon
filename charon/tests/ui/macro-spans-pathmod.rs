//@ ignore
// Loaded by `macro-spans.rs` with `#[path]`.
pub fn in_pathmod() -> u32 {
    5
}

macro_rules! make_fn_pathmod {
    ($name:ident) => {
        pub fn $name() -> u32 {
            6
        }
    };
}
pub(crate) use make_fn_pathmod;
make_fn_pathmod!(from_pathmod_local);
