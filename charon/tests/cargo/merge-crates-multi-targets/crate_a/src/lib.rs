/// Differs across targets: becomes a target dispatch.
#[cfg(target_pointer_width = "64")]
pub fn width() -> u32 {
    64
}
#[cfg(target_pointer_width = "32")]
pub fn width() -> u32 {
    32
}

#[cfg(target_pointer_width = "64")]
pub struct OnlyOn64;

pub fn same() -> u32 {
    0
}
