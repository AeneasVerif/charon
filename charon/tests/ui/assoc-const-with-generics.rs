struct V<const N: usize, T> {
    x: [T; N],
}

impl<const N: usize, T> V<N, T> {
    const LEN: usize = N; // This has generics <N, T>
}

trait HasLen {
    const LEN: usize;
}

impl<const N: usize> HasLen for [(); N] {
    const LEN: usize = N;
}

impl<const N: usize> HasLen for [bool; N] {
    const LEN: usize = N + 1;
}

pub trait HasDefaultLen<const M: usize> {
    const LEN: usize = M;
}

impl<const N: usize> HasDefaultLen<N> for [(); N] {}

impl<const N: usize> HasDefaultLen<N> for [bool; N] {
    // Recursive constant because we can
    const LEN: usize = if true {
        N
    } else {
        <Self as HasDefaultLen<N>>::LEN
    };
}
