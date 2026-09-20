//@ known-failure
//@ aux-crate=extern-static-no-initializer-aux.rs
//@ charon-args=--consts values
extern "C" {
    static LOCAL: i32;
}

fn main() {
    let _ = unsafe { LOCAL };
    let _ = unsafe { extern_static_no_initializer_aux::FOREIGN };
}
