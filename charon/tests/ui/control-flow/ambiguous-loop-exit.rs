pub fn f(x: u32) -> u32 {
    'outer: loop {
        if x == 3 {
            break 3;
        }

        loop {
            match if x == 0 {
                0
            } else if x == 1 {
                1
            } else {
                2
            } {
                0 => continue,
                1 => continue 'outer,
                _ => break 'outer 2,
            }
        }
    }
}
