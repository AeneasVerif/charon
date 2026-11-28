//@ aux-crate=foreign-linkage-attr-aux.rs
#![feature(linkage)]
extern crate foreign_linkage_attr_aux as aux;

unsafe extern "C" {
    #[linkage = "extern_weak"]
    static local_extern_weak_static: Option<unsafe extern "C" fn()>;
}

fn main() {
    unsafe {
        let _ = local_extern_weak_static;
        let _ = aux::dep_extern_weak_static;
        aux::dep_extern_weak_fn();
        let _ = aux::DEP_WEAK_STATIC;
        aux::dep_weak_fn();
    }
}
