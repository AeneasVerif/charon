cargo +nightly build

https://github.com/rust-lang/polonius/blob/master/inputs/clap-rs/README.md
cargo +YOUR_RUSTC rustc -- -Znll-facts -Ztime-passes -Zborrowck=mir

How to use Polonius:
cargo +nightly rustc -- -Zpolonius

Tests:
cargo +nightly rustc -- --test -Zpolonius
cd target/debug/ && .tests
