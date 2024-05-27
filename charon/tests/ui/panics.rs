#[allow(unreachable_code)]
fn panic1() {
    panic!();
}
fn panic2() {
    panic!("O no!");
}
fn panic3() {
    panic!("O {}!", "no");
}
fn panic4() {
    assert!(false);
}
fn panic5() {
    unreachable!();
}
fn panic6() {
    todo!();
}
fn panic7() {
    ::std::rt::begin_panic("explicit panic");
}
