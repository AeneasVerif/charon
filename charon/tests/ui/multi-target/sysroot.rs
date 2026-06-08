//@ charon-args=--start-from=core::ascii::escape_default --include=core::ascii::escape_default
//@ charon-args=--targets=x86_64-unknown-linux-gnu,x86_64-pc-windows-msvc,aarch64-apple-darwin,i686-unknown-linux-gnu
// This tests that we use a sysroot that has full MIR: that function has no MIR in the default sysroot.
