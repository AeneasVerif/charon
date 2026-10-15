pub trait Processor<'x> {
    fn process<'a>(&self, input: &'a u32) -> &'a u32;
}

pub fn call<'a, 'x>(processor: &dyn Processor<'x>, input: &'a u32) -> &'a u32 {
    processor.process(input)
}
