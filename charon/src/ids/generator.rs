use index_vec::Idx;
use std::{collections::HashMap, hash::Hash, marker::PhantomData};

#[derive(Debug, Clone, Copy)]
pub struct Generator<I: Idx> {
    counter: usize,
    phantom: PhantomData<I>,
}

impl<I: Idx> Generator<I> {
    pub fn new() -> Self {
        Self::new_with_init_value(0)
    }

    pub fn new_with_init_value(counter: usize) -> Self {
        Generator {
            counter,
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

#[derive(Debug, Clone)]
pub struct MapGenerator<K: Eq + Hash + Ord, I: Idx> {
    counter: Generator<I>,
    map: HashMap<K, I>,
}

impl<K: Eq + Hash + Ord, I: Idx> MapGenerator<K, I> {
    pub fn new() -> Self {
        MapGenerator {
            counter: Generator::new(),
            map: HashMap::new(),
        }
    }

    pub fn insert(&mut self, k: K) -> I {
        *self.map.entry(k).or_insert_with(|| self.counter.fresh_id())
    }

    pub fn get(&self, k: &K) -> Option<I> {
        self.map.get(k).map(|id| *id)
    }

    // We may need to generate fresh ids without inserting a value in the map
    pub fn fresh_id(&mut self) -> I {
        self.counter.fresh_id()
    }
}
