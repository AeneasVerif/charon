use std::borrow::Cow;
type Foo = usize;
type Generic<'a, T> = &'a T;
type Generic2<'a, T: Clone> = Cow<'a, [T]>;
