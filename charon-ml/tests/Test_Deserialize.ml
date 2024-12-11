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

  (* List the LLBC files.

     Remark: we do not deserialize the ULLBC files anymore: we rely on some
     micro-passes which are only performed on LLBC to remove some unwanted
     variants/types.
  *)
  let llbc_files = get_files_with_suffix folder ".llbc" in

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
            (* Test that pretty-printing doesn't crash *)
            let printed = PrintLlbcAst.Crate.crate_to_string m in
            log#ldebug (lazy ("\n" ^ printed ^ "\n")))
      llbc_files
  in

  (* Done *)
  ()
