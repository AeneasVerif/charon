pub fn run(input: &mut [u8]) -> Result<usize, dependency::Error> {
    let (kind, data) = dependency::split(input)?;
    Ok(kind.len() + data.len())
}
