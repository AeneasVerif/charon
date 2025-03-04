//@ charon-args=--monomorphize

fn main() {
    let res: Result<u32, u32> = Ok(0);
    let Ok(n) = res else { panic!() };
}
