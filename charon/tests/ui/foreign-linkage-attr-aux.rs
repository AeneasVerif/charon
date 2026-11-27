//@ ignore
#![feature(linkage)]

unsafe extern "C" {
    #[linkage = "extern_weak"]
    pub static dep_extern_weak_static: Option<unsafe extern "C" fn()>;
    #[linkage = "extern_weak"]
    pub fn dep_extern_weak_fn();
}

#[linkage = "weak"]
pub static DEP_WEAK_STATIC: u8 = 0;

#[linkage = "weak"]
pub fn dep_weak_fn() {}
