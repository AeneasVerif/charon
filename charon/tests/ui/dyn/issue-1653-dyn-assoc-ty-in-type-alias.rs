pub type Callback = dyn FnMut(usize);
pub type HKCallback = dyn for<'a> Fn(&'a usize) -> &'a usize;
