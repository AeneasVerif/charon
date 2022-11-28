struct Sheep { naked: bool, id: u32 }

trait Animal {
    // Associated function signature; `Self` refers to the implementor type.
    fn new(id: u32) -> Self;

    fn my_id(&self) -> u32;

    // Traits can provide default method definitions.
    fn talk(&self) {
        println!("I am {}", self.my_id());
    }
}

impl Sheep {
    fn is_naked(&self) -> bool {
        self.naked
    }

    fn shear(&mut self) {
        if self.is_naked() {
            // Implementor methods can use the implementor's trait methods.
            println!("{} is already naked...", self.my_id());
        } else {
            println!("{} gets a haircut!", self.my_id());

            self.naked = true;
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
    fn talk(&self) {
        // For example, we can add some quiet contemplation.
        println!("{} pauses briefly...", self.id);
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
