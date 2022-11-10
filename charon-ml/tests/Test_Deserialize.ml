open Charon
open Logging
module EL = Easy_logging.Logging

let log = main_log

(* Run the tests *)
let run_tests (folder : string) : unit =
  (* Retrieve the files in a directory which end with a proper suffix *)
  let get_files_with_suffix (folder : string) (suffix : string) : string list =
    Sys.readdir folder |> Array.to_list
    |> List.filter (fun file -> Filename.check_suffix file suffix)
  in

  (* List the ULLBC and LLBC files *)
  let ullbc_files = get_files_with_suffix folder ".ullbc" in
  let llbc_files = get_files_with_suffix folder ".llbc" in

  (* Deserialize ULLBC *)
  let () =
    List.iter
      (fun file ->
        log#ldebug (lazy ("Deserializing ULLBC file: " ^ file));
        (* Load the module *)
        let json = Yojson.Basic.from_file (folder ^ "/" ^ file) in
        match UllbcOfJson.crate_of_json json with
        | Error s ->
            log#error "Error when deserializing file %s: %s\n" file s;
            exit 1
        | Ok m ->
            log#linfo (lazy ("Deserialized: " ^ file));
            log#ldebug
              (lazy ("\n" ^ PrintUllbcAst.Crate.crate_to_string m ^ "\n")))
      ullbc_files
  in

  (* Deserialize LLBC *)
  let () =
    List.iter
      (fun file ->
        log#ldebug (lazy ("Deserializing LLBC file: " ^ file));
        (* Load the module *)
        let json = Yojson.Basic.from_file (folder ^ "/" ^ file) in
        match LlbcOfJson.crate_of_json json with
        | Error s ->
            log#error "Error when deserializing file %s: %s\n" file s;
            exit 1
        | Ok m ->
            log#linfo (lazy ("Deserialized: " ^ file));
            log#ldebug
              (lazy ("\n" ^ PrintLlbcAst.Crate.crate_to_string m ^ "\n")))
      llbc_files
  in

  (* Done *)
  ()
