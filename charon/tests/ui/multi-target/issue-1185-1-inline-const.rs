//@ charon-args=--targets=x86_64-unknown-linux-gnu,i686-unknown-linux-gnu
pub fn const_time_array_copy_mwe<const N: usize>(_a: &mut [u8; N]) {
    const {
        assert!(N <= u32::MAX as usize);
    }
}
