pub fn sum(s: &[u32]) -> u32 {
    // Comment1
    let mut sum = 0;
    // Comment2
    let mut i = 0;
    // Comment3
    while i < s.len() {
        // Comment4
        sum += s[i];
        // Comment5
        i += 1;
    }
    // Comment6
    sum = if sum > 10 {
        // Comment7
        sum + 100
    } else {
        // Comment8
        sum
    };
    // Comment9
    sum
}
