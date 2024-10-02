(** WARNING: this file is partially auto-generated. Do not edit `src/Meta.ml`
    by hand. Edit `templates/Meta.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `templates/Meta.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)
(** Meta data like code spans *)

type path_buf = string
[@@deriving show, ord]

(* __REPLACE0__ *)
[@@deriving show, ord]

(** Ordered file name *)
module OrderedFileName : Collections.OrderedType with type t = file_name =
struct
  type t = file_name

  let compare = compare_file_name
  let to_string s = show_file_name s
  let pp_t fmt s = pp_file_name fmt s
  let show_t s = show_file_name s
end

module FileNameSet = Collections.MakeSet (OrderedFileName)
module FileNameMap = Collections.MakeMap (OrderedFileName)
