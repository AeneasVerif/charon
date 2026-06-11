mod generate_ml;
mod generate_rust;

fn main() -> anyhow::Result<()> {
    generate_ml::main()?;
    generate_rust::main()
}
