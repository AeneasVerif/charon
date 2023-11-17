open Name_matcher_parser.Interface

let run_tests () =
  (* let _ = parse_name "T::X" in *)
  let _ = parse_name "x" in
  let _ = parse_name "{@T1}" in
  let _ = parse_name "asaf1::{@T1}" in
  let _ = parse_name "asaf1::{[@T]}" in
  let _ = parse_name "asaf1::{[@T; @C]}" in
  ()
