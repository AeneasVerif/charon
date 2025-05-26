open Charon
open Logging
module EL = Easy_logging.Logging

let log = main_log

(** [dir_is_empty dir] is true, if [dir] contains no files except
 * "." and ".."
 *)
let dir_is_empty dir = Array.length (Sys.readdir dir) = 0

(** [dir_contents] returns the paths of all regular files that are
 * contained in [dir]. Each file is a path starting with [dir].
 * From https://gist.github.com/lindig/be55f453026c65e761f4e7012f8ab9b5
 *)
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

(* Run the tests *)
let run_tests (folder : string) : unit =
  (* List the LLBC files.

     Remark: we do not deserialize the ULLBC files.
  *)
  let llbc_files =
    dir_contents folder
    |> List.filter (fun file -> Filename.check_suffix file ".llbc")
  in

  (* Deserialize LLBC *)
  let () =
    List.iter
      (fun file ->
        log#ldebug (lazy ("Deserializing LLBC file: " ^ file));
        (* Load the module *)
        let json = Yojson.Basic.from_file file in
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
