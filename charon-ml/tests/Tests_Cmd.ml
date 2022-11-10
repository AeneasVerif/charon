(** Tests, for the command line *)

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
let log = main_log
let () = log#set_level (if debug then EL.Debug else EL.Info)

(* Run the tests *)
let () = All_tests.Test_Deserialize.run_tests folder
