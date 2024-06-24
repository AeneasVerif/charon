//@ known-failure
#![feature(register_tool)]
#![register_tool(charon)]
#![register_tool(aeneas)]

#[charon::rename("")]
type TestEmpty = ();

#[charon::rename("Test!976?")]
type TestNonAlphanumeric = ();

#[charon::rename("75Test")]
type TestNotStartingWithLetter = ();

#[charon::rename(aaaa)]
type TestNotQuoted = ();

#[charon::rename("_Type36")]
#[aeneas::rename("_Type37")]
type TestMultiple = ();

#[charon::something_else("_Type36")]
type TestUnrecognizedArg = ();
