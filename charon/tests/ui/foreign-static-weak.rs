#![feature(linkage)]

unsafe extern "C" {
    #[linkage = "extern_weak"]
    static weak_fn: Option<unsafe extern "C" fn(i32) -> i32>;
    #[linkage = "extern_weak"]
    static weak_data: *mut u8;
    #[linkage = "extern_weak"]
    #[link_name = "real_weak_renamed"]
    static weak_renamed: *const u8;
}

fn main() {
    let f = unsafe { weak_fn };
    let d = unsafe { weak_data };
}
