use crate1 as _;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
}
