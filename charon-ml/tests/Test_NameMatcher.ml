open Name_matcher_parser.Interface

let run_tests () =
  (* let _ = parse_pattern "T::X" in *)
  let _ = parse_pattern "x" in
  let _ = parse_pattern "{@T1}" in
  let _ = parse_pattern "asaf1::{@T1}" in
  let _ = parse_pattern "asaf1::{[@T]}" in
  let _ = parse_pattern "asaf1::{[@T; @C]}" in
  let _ = parse_pattern "x::{&@R @T1}" in
  let _ = parse_pattern "x::{&@R mut @T1}" in
  let _ = parse_pattern "{Box<@T>}" in
  let _ = parse_pattern "alloc::{Box<@T>}::new" in
  let _ = parse_pattern "alloc::{Foo<@T, @C>}::new" in
  ()
