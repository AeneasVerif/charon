#![feature(extern_types)]
extern "C" {
    fn foo(x: i32);
    static CONST: u8;
    type Type;
    #[link_name = "real_bar"]
    fn bar();
    #[link_name = "REAL_STATIC"]
    static STATIC: u8;
}

fn use_type(_x: &Type) {}
