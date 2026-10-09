//@ ignore
#[macro_export]
macro_rules! make_fn_aux {
    ($name:ident) => {
        pub fn $name() -> u32 {
            2
        }
    };
}
