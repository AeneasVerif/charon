//@ known-failure
fn get<'a>(x: &'a u32) -> Option<&'a u32>
where
    &'a ():,
{
    Some(x)
}
