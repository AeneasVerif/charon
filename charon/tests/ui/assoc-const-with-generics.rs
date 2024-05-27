struct V<const N: usize, T> {
    x: [T; N],
}

impl<const N: usize, T> V<N, T> {
    const LEN: usize = N; // This has generics <N, T>
}
