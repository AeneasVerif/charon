struct Sheep { naked: bool, id: u32 }

trait Animal {
    // Associated function signature; `Self` refers to the implementor type.
    fn new(id: u32) -> Self;

    fn my_id(&self) -> u32;

    // Traits can provide default method definitions.
    fn talk(&self) -> u32 {
      return 23; 
    }
}

impl Sheep {
    fn is_naked(&self) -> bool {
        self.naked
    }

    fn shear(&mut self) -> u32 {
        if self.is_naked() {
            // Implementor methods can use the implementor's trait methods.
            self.my_id()
        } else {
            self.naked = true;
            self.my_id() + 1

        }
    }
}

// Implement the `Animal` trait for `Sheep`.
impl Animal for Sheep {
    // `Self` is the implementor type: `Sheep`.
    fn new(id: u32) -> Sheep {
        Sheep { id: id, naked: false }
    }

    fn my_id(&self) -> u32 {
        self.id
    }

    // Default trait methods can be overridden.
    fn talk(&self) -> u32 {
        // For example, we can add some quiet contemplation.
        12
    }
}

fn main() {
    // Type annotation is necessary in this case.
    let mut dolly: Sheep = Animal::new(23);
    // TODO ^ Try removing the type annotations.

    dolly.talk();
    dolly.shear();
    dolly.talk();
}
