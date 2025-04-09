//@ charon-args=--monomorphize --ullbc --print-ullbc --no-serialize
// Ensures monomorphization handles globals with generics

struct Foo<T> {
    value: T,
}

static FooInt: Foo<i32> = Foo { value: 0i32 };
static FooBool: Foo<bool> = Foo { value: false };

fn main() {
    let _b = FooBool.value;
}
