//! Regression test: nested for-loops with `--mir elaborated` must produce idiomatic LLBC
//! (inner loop exits with `break 0`, not `continue 1`).
//!
//! With `--mir elaborated`, drop elaboration inserts per-call unwind blocks. This causes
//! the `undefined_behavior` block (from match fallthrough) to be shared across inner and
//! outer switches, making it not dominated by the inner loop header. The dominance filter
//! in `compute_loop_exits` must ignore error-only blocks when deciding whether non-dominated
//! candidates exist, otherwise it discards the real exit and produces `continue 1`.
//@ charon-args=--mir elaborated

pub fn nested_for_complex(a: &mut [[u32; 5]; 5]) {
    let old = *a;
    for i in 0..5usize {
        for j in 0..5usize {
            a[i][j] = old[i][j] ^ old[i][(j + 1) % 5];
        }
    }
}
