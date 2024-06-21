open Charon
open Charon.Expressions
open Charon.LlbcAst
open Charon.Meta
open Logging
open NameMatcher

let log = main_log

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
      "{fn ()}";
      "{fn (@T, @U)}";
      "{fn (@T, @U) -> u32}";
      "{*const @T}";
      "{*mut @T}";
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

(* Annotations in rust code like `#[pattern::pass("<pattern>")]`. The exact syntax is:
   - `#[pattern::pass("<pattern>")]`: the item name must match that pattern.
   - `#[pattern::pass(call[<number>], "<pattern>")]`: for functions only; the
          `number`th `Call` statement must match that pattern.
   And the same with `fail` instead of `pass` for negative tests.
*)
module PatternTest = struct
  type t = { pattern : pattern; call_idx : int option; success : bool }

  type env = {
    ctx : ctx;
    match_config : match_config;
    fmt_env : PrintLlbcAst.fmt_env;
    print_config : print_config;
    to_pat_config : to_pat_config;
  }

  let mk_env (ctx : ctx) : env =
    let tgt = TkPattern in
    let match_with_trait_decl_refs = true in
    {
      ctx;
      match_config = { map_vars_to_vars = false; match_with_trait_decl_refs };
      print_config = { tgt };
      fmt_env = ctx_to_fmt_env ctx;
      to_pat_config = { tgt; use_trait_decl_refs = match_with_trait_decl_refs };
    }

  (* Parse a test from the annotation string as given by Charon. *)
  let parse (whole_attribute : string) : t option =
    match Core.String.chop_prefix whole_attribute ~prefix:"pattern::" with
    | None -> None
    | Some attribute -> (
        let re =
          Re.compile
            (Re.Pcre.re
               "^(pass|fail)\\((call\\s*\\[(\\d+)\\],\\s*)?\"(.*)\"\\)$")
        in
        match Re.exec_opt re attribute with
        | Some groups ->
            let success = Re.Group.get groups 1 = "pass" in
            let call_idx =
              Option.map int_of_string (Re.Group.get_opt groups 3)
            in
            let pattern = parse_pattern (Re.Group.get groups 4) in
            Some { pattern; call_idx; success }
        | None ->
            failwith ("Couldn't parse attribute: `" ^ whole_attribute ^ "`"))

  (* Check that the given function declaration matches the pattern. *)
  let check_fun_decl (env : env) (decl : fun_decl) (test : t) : bool =
    let fn_ptr =
      match test.call_idx with
      | None ->
          {
            func = FunId (FRegular decl.def_id);
            generics = Charon.TypesUtils.empty_generic_args;
          }
      | Some idx ->
          (* Find the nth function call in the function body. *)
          let rec list_calls (statement : statement) : call list =
            match statement.content with
            | Call call -> [ call ]
            | Sequence (st1, st2) -> list_calls st1 @ list_calls st2
            | Switch _ | Loop _ ->
                failwith
                  "Switches and loops are unsupported in name matcher tests"
            | _ -> []
          in
          let calls = list_calls (Option.get decl.body).body in
          let fn_ptrs =
            List.map
              (fun call ->
                match call.func with
                | FnOpRegular fn_ptr -> fn_ptr
                | FnOpMove _ ->
                    failwith
                      "Indirect calls are unsupported un name matcher tests")
              calls
          in
          List.nth fn_ptrs idx
    in
    let match_success =
      match_fn_ptr env.ctx env.match_config test.pattern fn_ptr
    in
    if test.success && not match_success then (
      log#error "Pattern %s failed to match function %s\n"
        (pattern_to_string env.print_config test.pattern)
        (pattern_to_string env.print_config
           (fn_ptr_to_pattern env.ctx env.to_pat_config decl.signature.generics
              fn_ptr));
      false)
    else if (not test.success) && match_success then (
      log#error "Pattern %s matches function %s but shouldn't\n"
        (pattern_to_string env.print_config test.pattern)
        (PrintTypes.name_to_string env.fmt_env decl.name);
      false)
    else true
end

(* This reads the output generated from the `ui/name-matcher-tests.rs` test
   file, and verifies that for each `#[pattern::...]` annotation, the item
   matches the pattern. See the `PatternTest` module for details of what
   annotations are available. *)
let annotated_rust_tests test_file =
  (* We read the llbc file generated from the annotated rust file. *)
  log#ldebug (lazy ("Deserializing LLBC file: " ^ test_file));
  let json = Yojson.Basic.from_file test_file in
  let (crate : crate) =
    match LlbcOfJson.crate_of_json json with
    | Error s ->
        log#error "Error when deserializing file %s: %s\n" test_file s;
        exit 1
    | Ok crate -> crate
  in

  (* We look through all declarations for our special attributes and check each case. *)
  let ctx = ctx_from_crate crate in
  let env = PatternTest.mk_env ctx in
  let all_pass =
    T.FunDeclId.Map.for_all
      (fun _ (decl : fun_decl) ->
        let attrs =
          List.filter_map
            (function AttrUnknown attr -> Some attr | _ -> None)
            decl.item_meta.attr_info.attributes
        in
        let tests = List.filter_map PatternTest.parse attrs in
        let test_results =
          List.map (PatternTest.check_fun_decl env decl) tests
        in
        List.for_all (fun b -> b) test_results)
      crate.fun_decls
  in

  if all_pass then log#linfo (lazy "Name matcher tests: success") else exit 1

let run_tests test_file =
  parse_tests ();
  name_map_tests ();
  annotated_rust_tests test_file
