fn main() {
  let a = || 42;
  let dyn_a: &dyn Fn() -> i32 = &a;
}