//@ charon-args=--extract-opaque-bodies
//@ charon-args=--sysroot=default

fn unwrap(res: Result<u32, u32>) -> u32 {
    res.unwrap()
}
