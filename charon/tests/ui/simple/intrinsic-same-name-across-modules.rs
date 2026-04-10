#![feature(intrinsics)]
#![feature(core_intrinsics)]

mod first {
    pub mod nested {
        #[rustc_intrinsic]
        #[inline]
        pub const fn wrapping_add<T: Copy>(lhs: T, rhs: T) -> T;

        pub fn call() -> u8 {
            unsafe { wrapping_add(1, 2) }
        }
    }
}

fn call() -> u8 {
    unsafe { std::intrinsics::wrapping_add(3, 4) }
}
