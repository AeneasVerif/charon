use std::{env, fs, path::Path};

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest = Path::new(&out_dir).join("generated.rs");
    fs::write(
        &dest,
        "pub struct Generated {\n    pub value: u32,\n}\n\n\
         pub fn make() -> Generated {\n    Generated { value: 0 }\n}\n",
    )
    .unwrap();
    println!("cargo:rerun-if-changed=build.rs");
}
