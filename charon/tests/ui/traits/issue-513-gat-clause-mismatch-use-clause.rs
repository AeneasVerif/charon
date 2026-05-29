trait HasAssoc {
    type Assoc;
}
trait AlsoHasAssoc: HasAssoc {}

impl HasAssoc for () {
    type Assoc = u32;
}
impl AlsoHasAssoc for () {}

trait Trait: Sized {
    type Type: PartialEq<Self::Assoc>
    where
        Self: HasAssoc;
}

impl Trait for () {
    type Type
        = u32
    where
        Self: AlsoHasAssoc;
}
