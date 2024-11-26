pub fn fun1() {
    crate::opaque::fun2()
}

pub fn fun3() {
    let _ = core::ptr::null::<u8>();
    let _ = crate::opaque::custom_null::<u8>();
}
