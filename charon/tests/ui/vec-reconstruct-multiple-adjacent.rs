fn multiple_adjacent() {
    let _a = vec![1u8];
    let _b = vec![2u8];
    let _c = vec![3u8];
}

fn multiple_values() {
    let _a = vec![1u8, 2u8, 3u8];
}

fn with_fn_calls() {
    fn foo() -> u8 {
        42
    }
    let _a = vec![foo(), foo()];
}

fn repeated() {
    let _a = vec![1u8; 3];
}
