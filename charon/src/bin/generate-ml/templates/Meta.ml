(** WARNING: this file is partially auto-generated. Do not edit `src/Meta.ml`
    by hand. Edit `templaces/Meta.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `templaces/Meta.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)
(** Meta data like code spans *)

type path_buf = string
(* __REPLACE0__ *)
[@@deriving show, ord]

(** Span data *)
type raw_span = { file : file_name; beg_loc : loc; end_loc : loc }
[@@deriving show, ord]

type __meta_1 = unit (* to start the recursive group *)
(* __REPLACE1__ *)
[@@deriving show, ord]
