//@ known-failure
pub fn closure() {
    let _ = |_: &dyn Fn(Box<dyn Send + 'static>)| ();
}
