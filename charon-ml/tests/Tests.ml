open Charon
open Logging
module EL = Easy_logging.Logging

(* Set the log level *)
let log = main_log
let () = log#set_level EL.Info

(* Call the tests *)
let () = All_tests.Test_Deserialize.run_tests "../../../tests/serialized"
