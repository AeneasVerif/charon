(** The main source *)
let main_log = Logs.Src.create "charon" ~doc:"Charon"

(** Source for LlbcOfJson *)
let llbc_of_json_logger =
  Logs.Src.create "charon.llbc_of_json" ~doc:"Deserialization of LLBC files"

(** Source for NameMatcher *)
let name_matcher_logger =
  Logs.Src.create "charon.name_matcher"
    ~doc:"Matching of names against patterns"

(** The ANSI escape sequence which sets the foreground color used to display a
    given level. *)
let level_color (lvl : Logs.level) : string =
  let code =
    match lvl with
    | App -> 95 (* light magenta *)
    | Error -> 91 (* light red *)
    | Warning -> 93 (* light yellow *)
    | Info -> 92 (* light green *)
    | Debug -> 94 (* light blue *)
  in
  Printf.sprintf "\027[%dm" code

(** The ANSI escape sequence which resets the foreground color *)
let color_reset = "\027[39m"

let show_level : Logs.level -> string = function
  | App -> "Flash"
  | Error -> "Error"
  | Warning -> "Warn"
  | Info -> "Info"
  | Debug -> "Debug"

(** A reporter which prints the messages on [ppf], prefixed with their level and
    the name of their source. *)
let reporter (ppf : Format.formatter) : Logs.reporter =
  let report src lvl ~over k msgf =
    let k _ =
      over ();
      k ()
    in
    msgf @@ fun ?header:_ ?tags:_ fmt ->
    Format.pp_set_max_indent ppf 200;
    Format.kfprintf k ppf
      ("@[[%s%-5s%s] [%s] @[" ^^ fmt ^^ "@]@]@.")
      (level_color lvl) (show_level lvl) color_reset (Logs.Src.name src)
  in
  { Logs.report }

let () =
  Logs.set_reporter (reporter Format.std_formatter);
  Logs.set_level ~all:true (Some Logs.Info)
