open Charon
open Logging
module EL = Easy_logging.Logging

(* Set the log level - we use the environment variable "CHARON_LOG" *)
let log = main_log

let () =
  try
    let _ = Unix.getenv "CHARON_LOG" in
    log#set_level EL.Debug
  with Not_found -> log#set_level EL.Info

(* Call the tests *)
let () = Test_Deserialize.run_tests "../../../tests/serialized"
let () = Test_NameMatcher.run_tests ()
