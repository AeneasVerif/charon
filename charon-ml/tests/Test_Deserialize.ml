open Charon
open Logging
module EL = Easy_logging.Logging

let log = main_log

(** [dir_is_empty dir] is true, if [dir] contains no files except * "." and ".."
*)
let dir_is_empty dir = Array.length (Sys.readdir dir) = 0

(** [dir_contents] returns the paths of all regular files that are * contained
    in [dir]. Each file is a path starting with [dir]. * From
    https://gist.github.com/lindig/be55f453026c65e761f4e7012f8ab9b5 *)
let dir_contents dir =
  let rec loop result = function
    | f :: fs when Sys.is_directory f ->
        Sys.readdir f |> Array.to_list
        |> List.map (Filename.concat f)
        |> List.append fs |> loop result
    | f :: fs -> loop (f :: result) fs
    | [] -> result
  in
  loop [] [ dir ]

let string_contains ~(sub : string) (s : string) : bool =
  try
    let re = Str.regexp_string sub in
    ignore @@ Str.search_forward re s 0;
    true
  with Not_found -> false

let assert_eq x y msg arg_to_string =
  if x <> y then
    Format.kasprintf failwith "Real: %s, Expected: %s for %s" (arg_to_string x)
      (arg_to_string y) msg

let assert_contains ~msg ~sub s =
  if not (string_contains ~sub s) then
    Format.kasprintf failwith "%s, expected substring: '%s' in '%s'" msg sub s

let read_all (ic : in_channel) : string =
  let buf = Buffer.create 4096 in
  (try
     while true do
       Buffer.add_string buf (input_line ic);
       Buffer.add_char buf '\n'
     done
   with End_of_file -> ());
  Buffer.contents buf

let command_output ?(allow_failure = false) (cmd : string) (args : string list)
    : string =
  let cmdline = String.concat " " (List.map Filename.quote (cmd :: args)) in
  let stdout, stdin, stderr =
    Unix.open_process_full cmdline (Unix.environment ())
  in
  close_out stdin;
  let out = read_all stdout in
  let err = read_all stderr in
  match Unix.close_process_full (stdout, stdin, stderr) with
  | Unix.WEXITED 0 -> out
  | Unix.WEXITED _ when allow_failure -> out ^ err
  | Unix.WEXITED code ->
      Format.kasprintf failwith "Command failed (%d): %s\n%s" code cmdline err
  | Unix.WSIGNALED signal ->
      Format.kasprintf failwith "Command signaled (%d): %s\n%s" signal cmdline
        err
  | Unix.WSTOPPED signal ->
      Format.kasprintf failwith "Command stopped (%d): %s\n%s" signal cmdline
        err

let charon_bin =
  try Unix.getenv "CHARON_BIN"
  with Not_found ->
    (* Dune runs this test from [_build/default/charon-ml/tests]. *)
    "../../../../bin/charon"

let normalize_trailing_newlines (s : string) : string =
  let rec last_non_newline i =
    if i < 0 then -1 else if s.[i] = '\n' then last_non_newline (i - 1) else i
  in
  String.sub s 0 (last_non_newline (String.length s - 1) + 1) ^ "\n"

let unified_diff ~(expected : string) ~(ocaml : string) : string =
  let expected_file = Filename.temp_file "charon-expected-pretty" ".out" in
  let ocaml_file = Filename.temp_file "charon-ocaml-pretty" ".out" in
  let write file contents =
    let oc = open_out file in
    output_string oc contents;
    close_out oc
  in
  write expected_file expected;
  write ocaml_file ocaml;
  let diff =
    command_output ~allow_failure:true "diff"
      [ "-u"; "--label"; "rust"; "--label"; "ocaml"; expected_file; ocaml_file ]
  in
  Sys.remove expected_file;
  Sys.remove ocaml_file;
  diff

let assert_pretty_matches_rust (file : string) (printed : string) : unit =
  let expected =
    command_output charon_bin [ "pretty-print"; "--format"; "postcard"; file ]
    |> normalize_trailing_newlines
  in
  let ocaml = normalize_trailing_newlines printed in
  if expected <> ocaml then
    let diff = unified_diff ~expected ~ocaml in
    Format.kasprintf failwith
      "OCaml pretty-printer output differs from %s pretty-print for %s:\n%s"
      charon_bin file diff

let test_cross_format_errors json postcard =
  (match OfPostcard.crate_of_postcard_file json with
  | Ok _ ->
      Format.kasprintf failwith
        "Expected postcard deserializer to reject JSON file: %s" json
  | Error e ->
      assert_contains ~msg:"Wrong error for JSON fed to Postcard"
        ~sub:"looks like JSON" e);
  (match OfJson.crate_of_json_file postcard with
  | Ok _ ->
      Format.kasprintf failwith
        "Expected JSON deserializer to reject postcard file: %s" postcard
  | Error e ->
      assert_contains ~msg:"Wrong error for Postcard fed to JSON"
        ~sub:"looks like Postcard" e);
  log#linfo
    (lazy
      (Printf.sprintf
         "Cross-format error tests passed for JSON file %s and Postcard file %s"
         json postcard))

(* Run the tests *)
let run_tests (folder : string) : unit =
  (* List the generated LLBC and ULLBC files. *)
  let json_files =
    dir_contents folder
    |> List.filter (fun file ->
           Filename.check_suffix file ".llbc"
           || Filename.check_suffix file ".ullbc")
    |> List.sort String.compare
  in
  let postcard_files =
    dir_contents folder
    |> List.filter (fun file ->
           Filename.check_suffix file ".llbc.postcard"
           || Filename.check_suffix file ".ullbc.postcard")
    |> List.sort String.compare
  in

  let json_time = ref 0.0 in
  let postcard_time = ref 0.0 in

  (* Deserialize (U)LLBC JSON files *)
  let () =
    List.iter
      (fun file ->
        log#ldebug (lazy ("Deserializing JSON file: " ^ file));
        (* Load the module *)
        let start_time = Unix.gettimeofday () in
        match OfJson.crate_of_json_file file with
        | Error s ->
            log#error "Error when deserializing file %s: %s\n" file s;
            exit 1
        | Ok _ ->
            json_time := !json_time +. (Unix.gettimeofday () -. start_time);
            log#linfo (lazy ("Deserialized: " ^ file)))
      json_files
  in
  let () =
    List.iter
      (fun file ->
        log#ldebug (lazy ("Deserializing postcard file: " ^ file));
        (* Load the module *)
        let start_time = Unix.gettimeofday () in
        match OfPostcard.crate_of_postcard_file file with
        | Error s ->
            log#error "Error when deserializing postcard file %s: %s\n" file s;
            exit 1
        | Ok m ->
            postcard_time :=
              !postcard_time +. (Unix.gettimeofday () -. start_time);
            log#linfo (lazy ("Deserialized postcard: " ^ file));
            let printed = Print.crate_to_string m in
            assert_pretty_matches_rust file printed)
      postcard_files
  in

  let avg_of time vals =
    if List.length vals > 0 then !time /. float_of_int (List.length vals)
    else 0.0
  in
  let avg_json_time = avg_of json_time json_files in
  let avg_postcard_time = avg_of postcard_time postcard_files in
  log#linfo
    (lazy
      (Printf.sprintf
         "Average deserialization time: JSON: %f seconds, Postcard: %f seconds \
          (%f times faster)"
         avg_json_time avg_postcard_time
         (if avg_postcard_time > 0.0 then avg_json_time /. avg_postcard_time
          else 0.0)));

  (* for each JSON and Postcard file pair, check the size of the file and print the ratio *)
  let ratios = ref [] in
  json_files
  |> List.iter (fun json_file ->
         let postcard_file = json_file ^ ".postcard" in
         if List.exists (fun f -> f = postcard_file) postcard_files then
           let json_size = (Unix.stat json_file).st_size in
           let postcard_size = (Unix.stat postcard_file).st_size in
           let ratio =
             if postcard_size > 0 then
               float_of_int json_size /. float_of_int postcard_size
             else 0.0
           in
           ratios := ratio :: !ratios);
  (* print min, max, avg and med ratios *)
  if !ratios = [] then ()
  else
    let min_ratio = List.fold_left min max_float !ratios in
    let max_ratio = List.fold_left max 0.0 !ratios in
    let avg_ratio =
      List.fold_left ( +. ) 0.0 !ratios /. float_of_int (List.length !ratios)
    in
    let sorted_ratios = List.sort compare !ratios in
    let med_ratio =
      if List.length sorted_ratios mod 2 = 1 then
        List.nth sorted_ratios (List.length sorted_ratios / 2)
      else
        let mid = List.length sorted_ratios / 2 in
        (List.nth sorted_ratios mid +. List.nth sorted_ratios (mid - 1)) /. 2.0
    in
    log#linfo
      (lazy
        (Printf.sprintf
           "Size ratio (JSON/Postcard): min: %f, max: %f, avg: %f, med: %f"
           min_ratio max_ratio avg_ratio med_ratio));

    match (json_files, postcard_files) with
    | json :: _, postcard :: _ -> test_cross_format_errors json postcard
    | _ ->
        log#linfo
          (lazy "No JSON or Postcard files found, skipping cross-format tests.");

        (* Done *)
        ()
