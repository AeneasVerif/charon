pub fn f() {
    let _x = 0;

    if false {
        return;
    }

    for v in 0..1 {
        if v == 0 {
            return;
        }
    }
}
