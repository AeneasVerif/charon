open Charon
open Logging
module EL = Easy_logging.Logging

(* Generate a backtrace upon failure *)
let () = Printexc.record_backtrace true

(* Read the command line arguments *)
let folder, debug =
  let debug = ref false in

  let spec = [ ("-debug", Arg.Set debug, " Output debugging information") ] in
  let spec = Arg.align spec in
  let folders = ref [] in
  let add_folder f = folders := f :: !folders in
  Arg.parse spec add_folder "";
  match !folders with
  | [ f ] -> (f, !debug)
  | _ ->
      print_string "We accept only one folder name arguments";
      exit 1

(* Set the log level *)
let () = main_log#set_level (if debug then EL.Debug else EL.Info)
let log = main_log

let get_files_with_suffix (folder : string) (suffix : string) : string array =
  Sys.readdir folder |> Array.to_seq
  |> Seq.filter (fun file -> Filename.check_suffix file suffix)
  |> Array.of_seq

(* List the ULLBC and LLBC files *)
let ullbc_files = get_files_with_suffix folder ".ullbc"
let llbc_files = get_files_with_suffix folder ".llbc"

(* Deserialize ULLBC *)
let () =
  Array.iter
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

(* Deserialize LLBC *)
let () =
  Array.iter
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
          log#ldebug (lazy ("\n" ^ PrintLlbcAst.Crate.crate_to_string m ^ "\n")))
    llbc_files
