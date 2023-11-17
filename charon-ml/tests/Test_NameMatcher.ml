open Name_matcher_parser.Interface

let run_tests () =
  let _ = parse_name_pattern "x" in
  let _ = parse_name_pattern "x::y" in
  let _ = parse_name_pattern "x::y1::Z2::a" in
  let _ = parse_name_pattern "{@T}" in
  let _ = parse_name_pattern "{@T1}" in
  let _ = parse_name_pattern "x::{@T1}" in
  let _ = parse_name_pattern "x::{[@T]}" in
  let _ = parse_name_pattern "x::{[@T; @C]}" in
  let _ = parse_name_pattern "x::{&@R @T1}" in
  let _ = parse_name_pattern "x::{&@R mut @T1}" in
  let _ = parse_name_pattern "{Box<@T>}" in
  let _ = parse_name_pattern "alloc::{Box<@T>}::new" in
  let _ = parse_name_pattern "alloc::{Foo<@T, @C>}::new" in
  let _ = parse_inst_name_pattern "core::slice::index::SliceIndex<@T1, @T2>" in
  let _ = parse_inst_name_pattern "core::slice::index::SliceIndex<Range>" in
  let _ =
    parse_inst_name_pattern "core::slice::index::SliceIndex<Range, [@T]>"
  in
  let _ =
    parse_inst_name_pattern "core::slice::index::SliceIndex<Range<usize>, [@T]>"
  in
  let _ = parse_name_pattern "{()}" in
  let _ = parse_name_pattern "{(@T, @T, Range<usize>)}" in
  ()
