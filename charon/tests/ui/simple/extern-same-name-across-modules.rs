extern "C" {
    fn same_name(x: i32) -> i32;
}

unsafe fn call_root() -> i32 {
    unsafe { same_name(0) }
}

mod first {
    unsafe extern "C" {
        fn same_name(x: i32) -> i32;
    }

    pub unsafe fn call() -> i32 {
        unsafe { same_name(1) }
    }
}

mod second {
    pub mod nested {
        unsafe extern "C" {
            fn same_name(x: i32) -> i32;
        }

        pub unsafe fn call() -> i32 {
            unsafe { same_name(2) }
        }
    }
}

mod local_impl {
    pub fn same_name(x: i32) -> i32 {
        x
    }

    pub fn call() -> i32 {
        same_name(3)
    }
}
