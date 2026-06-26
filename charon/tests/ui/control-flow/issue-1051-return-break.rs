pub fn f(mut y: u32) -> bool {
    if y > 0 {
        loop {
            if y == 0 {
                return true;
            }
            y -= 1;
            if y == 0 {
                break;
            }
        }
    }
    false
}
