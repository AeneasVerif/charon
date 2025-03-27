//@ charon-args=--remove-associated-types=*
trait Trait {
    type Assoc;
}

trait IntoIterator {
    type IntoIter: Trait<Assoc = ()>;
}

// We should be able to deduce that `Clause2_Assoc = ()`.
fn foo<I>()
where
    I: IntoIterator,
    I::IntoIter: Trait,
{
}
