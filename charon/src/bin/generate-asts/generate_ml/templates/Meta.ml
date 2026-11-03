(** WARNING: this file is partially auto-generated. Do not edit `src/Meta.ml`
    by hand. Edit `generate_ml/templates/Meta.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `generate_ml/templates/Meta.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-asts` in the crate root. The
    code-generation code is in `charon/src/bin/generate-asts`.
 *)

open Identifiers

module TypeDeclId = HashedIdGen ()
module GlobalDeclId = HashedIdGen ()
module TraitDeclId = HashedIdGen ()
module TraitImplId = HashedIdGen ()
module FunDeclId = HashedIdGen ()
module TraitMethodId = OrdIdGen ()
module AssocTypeId = OrdIdGen ()
module AssocConstId = OrdIdGen ()

type path_buf = string
[@@deriving show, ord, eq, hash]

(* __REPLACE0__ *)
