//@ known-failure
#![feature(register_tool)]
#![register_tool(charon)]
#![register_tool(aeneas)]

// Errors because rename attribute should not be empty
#[charon::rename("")]
type TestEmpty = i32;

// Errors because rename attribute should only contain alphanumeric or '_' characters
#[charon::rename("Test!976?")]
type TestNonAlphanumeric = i32;

// Errors because rename attribute should begin with a letter
#[charon::rename("75Test")]
type TestNotStartingWithLetter = i32;

// Errors because rename attribute is not of the proper shape (lacks "")
#[charon::rename()]
type TestNotProperShape = i32;
