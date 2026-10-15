//@ ignore
// Included by `macro-spans.rs`.
pub fn included() -> u32 {
    3
}

macro_rules! make_fn_included {
    ($name:ident) => {
        pub fn $name() -> u32 {
            4
        }
    };
}
make_fn_included!(from_included_local);
