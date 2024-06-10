//@ known-failure
//@ no-check-output

// Errors because rename attribute should not be empty
#[charon::rename()]
type TestEmpty = i32;

// Errors because rename attribute should only contain alphanumeric or '_' characters 
#[charon::rename(Test!976?)]
type TestNonAlphanumeric = i32;

// Errors because rename attribute should begin with a letter
#[charon::rename(75Test)]
type TestNotStartingWithLetter = i32;