use index_vec::Idx;
use std::marker::PhantomData;

#[derive(Debug, Clone, Copy)]
pub struct Generator<I: Idx> {
    counter: usize,
    phantom: PhantomData<I>,
}

impl<I: Idx> Generator<I> {
    pub fn new() -> Self {
        Self::new_with_init_value(I::from_usize(0))
    }

    pub fn new_with_init_value(index: I) -> Self {
        Generator {
            counter: index.index(),
            phantom: PhantomData,
        }
    }

    pub fn fresh_id(&mut self) -> I {
        let index = I::from_usize(self.counter);
        // The release version of the code doesn't check for overflows.
        // As the max usize is very large, overflows are extremely
        // unlikely. Still, it is extremely important for our code that
        // no overflows happen on the index counters.
        self.counter = self.counter.checked_add(1).unwrap();
        index
    }
}

// Manual impl to avoid the `I: Default` bound.
impl<I: Idx> Default for Generator<I> {
    fn default() -> Self {
        Self {
            counter: Default::default(),
            phantom: Default::default(),
        }
    }
}
