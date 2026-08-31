//@ no-default-options
//@ charon-args=--monomorphize --precise-drops --desugar-drops --include core::ptr::drop_in_place

trait T {}

unsafe fn f(p: *mut dyn T) {
    std::ptr::drop_in_place(p)
}
