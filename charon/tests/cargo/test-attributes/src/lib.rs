fn foo() {}

#[cfg(test)]
mod tests {
    #[test]
    fn test_foo() {
        super::foo();
    }

    #[test]
    #[should_panic]
    fn test_should_panic() {
        panic!("This test should panic");
    }

    #[test]
    #[ignore]
    fn test_ignore() {}
}
