open Name_matcher_parser.Interface

let run_tests () =
  let _ = parse_pattern "x" in
  let _ = parse_pattern "x::y" in
  let _ = parse_pattern "x::y1::Z2::a" in
  let _ = parse_pattern "{@T}" in
  let _ = parse_pattern "{@1}" in
  let _ = parse_pattern "x::{@T}" in
  let _ = parse_pattern "x::{[@T]}" in
  let _ = parse_pattern "x::{[@T; @N]}" in
  let _ = parse_pattern "x::{&'R @T1}" in
  let _ = parse_pattern "x::{&'R mut @T1}" in
  let _ = parse_pattern "{Box<@T>}" in
  let _ = parse_pattern "alloc::{Box<@T>}::new" in
  let _ = parse_pattern "alloc::{Foo<@T, @C>}::new" in
  let _ = parse_pattern "core::slice::index::SliceIndex<@T, @I>" in
  let _ = parse_pattern "core::slice::index::SliceIndex<Range>" in
  let _ = parse_pattern "core::slice::index::SliceIndex<Range, [@T]>" in
  let _ = parse_pattern "core::slice::index::SliceIndex<Range<usize>, [@T]>" in
  let _ = parse_pattern "{()}" in
  let _ = parse_pattern "{(@T, @T, Range<usize>)}" in
  ()
