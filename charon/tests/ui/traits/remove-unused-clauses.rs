trait Trait {}

fn callee<T: Trait>() {}

pub fn caller<T: Trait>() {
    callee::<T>();
}

pub fn recursive<T: Trait>() {
    if false {
        recursive::<T>();
    }
}

pub fn swap_recursive<T, U>()
where
    T: Copy,
    U: Copy,
{
    if false {
        swap_recursive::<U, T>();
    }
}

trait HasAssoc {
    type Assoc;
}
pub fn clause_dep<T>()
where
    T: HasAssoc,
    T::Assoc: Trait, // uses a sibling clause
{
    if false {
        clause_dep::<T>()
    }
}
