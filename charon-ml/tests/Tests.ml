(* Set the log level - we use the environment variable "CHARON_LOG" *)
let () =
  Printexc.record_backtrace true;
  let level =
    try
      let _ = Unix.getenv "CHARON_LOG" in
      Logs.Debug
    with Not_found -> Logs.Info
  in
  Logs.Src.set_level Charon.Logging.main_log (Some level)

let llbc_dir =
  try Unix.getenv "CHARON_TESTS_DIR" with Not_found -> "../../charon/tests/ui"

(* Call the tests *)
(* llbc files are copied into the `_build` dir by the `(deps)` rule in `./dune`. *)
let () = Test_Deserialize.run_tests llbc_dir
let () = Test_NameMatcher.run_tests (llbc_dir ^ "/ml-name-matcher-tests.llbc")

let () =
  Test_NameMatcher.run_tests (llbc_dir ^ "/ml-mono-name-matcher-tests.llbc")

let () =
  Test_NameMatcher.run_tests
    (llbc_dir ^ "/ml-multi-target-name-matcher-tests.llbc")

let () =
  Test_NameMatcher.run_tests
    (llbc_dir ^ "/ml-partial-mono-name-matcher-tests.llbc")
