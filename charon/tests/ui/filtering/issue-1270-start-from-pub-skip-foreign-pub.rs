//@ charon-args=--start-from-pub
pub fn example(x: Result<u32, String>) -> Result<u32, String> {
    Ok(x?)
}
