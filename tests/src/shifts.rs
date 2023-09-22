//! Exercise the translation of bit shifts
#![allow(dead_code)]

fn f(a: u32) -> u32 {
  let mut t = a >> 16;
  t <<= 2;
  t
}
