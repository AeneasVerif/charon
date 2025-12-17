fn main() {
  let i = 42;
  let ref_i = &i;
  let f = || *ref_i;
  let dyn_f: &dyn Fn() -> i32 = &f;
}