//@ known-failure
//@ charon-args=--lift-associated-types=*
pub trait HasAssoc {
    type Assoc;
}

pub struct NeedsAssoc<T: HasAssoc>(T);

impl HasAssoc for () {
    // Lifting this type visits NeedsAssoc<()>, which requires (): HasAssoc again.
    type Assoc = NeedsAssoc<()>;
}
