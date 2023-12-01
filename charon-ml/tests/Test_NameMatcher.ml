open Charon
open Logging
open NameMatcher

let log = main_log
let _ = log#linfo (lazy "Name matcher tests: starting")

let parse_tests () =
  let patterns : string list =
    [
      "x";
      "x::y";
      "x::y1::Z2::a";
      "{@T}";
      "{@1}";
      "x::{@T}";
      "x::{[@T]}";
      "x::{[@T; @N]}";
      "x::{&'R @T1}";
      "x::{&'R mut @T1}";
      "{Box<@T>}";
      "alloc::{Box<@T>}::new";
      "alloc::{Foo<@T, @C>}::new";
      "core::slice::index::SliceIndex<@T, @I>";
      "core::slice::index::SliceIndex<Range>";
      "core::slice::index::SliceIndex<Range, [@T]>";
      "core::slice::index::SliceIndex<Range<usize>, [@T]>";
      "{()}";
      "{(@T, @T, Range<usize>)}";
    ]
  in
  let _ = List.map parse_pattern patterns in
  ()

let name_map_tests () =
  let bindings =
    [
      "a";
      "a::b::{Type<@>}";
      "a::b::{Type<@T>}::c";
      "a::b::{Type<@>}::d";
      "a::b::{Type<@1>}::d::e";
      "a::b";
      "a::c";
      "a::{Type1<'a, @T>}::h";
      "a::{Type1<'b, @T>}::e";
    ]
  in
  let bindings = List.mapi (fun i p -> (parse_pattern p, i)) bindings in
  let m = NameMatcherMap.of_list bindings in
  List.iter
    (fun (p, i) -> assert (snd (NameMatcherMap.replace p (-1) m) = Some i))
    bindings

let run_tests () =
  parse_tests ();
  name_map_tests ()

let _ = log#linfo (lazy "Name matcher tests: success")
