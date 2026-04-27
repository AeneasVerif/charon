(** WARNING: this file is partially auto-generated. Do not edit `OfPostcard.ml`
    by hand. Edit `templates/OfPostcard.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `templates/OfPostcard.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)

open OfPostcardBasic
open Identifiers
open Generated_Meta
open Generated_Values
open Generated_Types
open Generated_Expressions
open Generated_GAst
open Generated_FullAst
open Scalars
module FileId = IdGen ()
module HashConsId = IdGen ()

module FileTbl = Hashtbl.Make (struct
  type t = FileId.id

  let equal = FileId.equal_id
  let hash = Hashtbl.hash
end)

type of_postcard_ctx = {
  id_to_file_map : file FileTbl.t;
  ty_hashcons_map : ty HashConsId.Map.t ref;
  tref_hashcons_map : trait_ref HashConsId.Map.t ref;
}

let empty_of_postcard_ctx : of_postcard_ctx =
  {
    id_to_file_map = FileTbl.create 8;
    ty_hashcons_map = ref HashConsId.Map.empty;
    tref_hashcons_map = ref HashConsId.Map.empty;
  }

let hash_consed_val_of_postcard (map : 'a HashConsId.Map.t ref)
    (of_postcard : of_postcard_ctx -> postcard_state -> ('a, string) result)
    (ctx : of_postcard_ctx) (st : postcard_state) : ('a, string) result =
  combine_error_msgs st __FUNCTION__
    (let* tag = int_of_postcard ctx st in
     match tag with
     | 0 ->
         let* id = HashConsId.id_of_postcard ctx st in
         let* v = of_postcard ctx st in
         map := HashConsId.Map.add id v !map;
         Ok v
     | 1 ->
         let* id = HashConsId.id_of_postcard ctx st in
         begin
           match HashConsId.Map.find_opt id !map with
           | Some v -> Ok v
           | None ->
               Error
                 "Hash-consing key not found; there is a serialization mismatch \
                  between Rust and OCaml"
         end
     | 2 -> of_postcard ctx st
     | _ -> Error "invalid hash-consed representation")

let path_buf_of_postcard = string_of_postcard

let opt_indexed_map_of_postcard :
    'a0 'a1.
    (of_postcard_ctx -> postcard_state -> ('a0, string) result) ->
    (of_postcard_ctx -> postcard_state -> ('a1, string) result) ->
    of_postcard_ctx ->
    postcard_state ->
    ('a1 option list, string) result =
 fun arg0_of_postcard arg1_of_postcard ctx st ->
  list_of_postcard (option_of_postcard arg1_of_postcard) ctx st

(* __REPLACE0__ *)

module Ullbc = struct
  open UllbcAst

  (* __REPLACE1__ *)
end

module Llbc = struct
  open LlbcAst

  (* __REPLACE2__ *)
end

(* __REPLACE3__ *)

let crate_of_postcard_file (file : string) : (GAst.crate, string) result =
  let* st = state_of_file file in
  let* charon_version = string_of_postcard () st in
  if not (String.equal charon_version CharonVersion.supported_charon_version) then
    Error
      ("Incompatible version of charon: this program supports llbc emitted by \
        charon v" ^ CharonVersion.supported_charon_version
     ^ " but attempted to read a file emitted by charon v" ^ charon_version
     ^ ".")
  else
    let ctx = empty_of_postcard_ctx in
    let* crate = translated_crate_of_postcard ctx st in
    let* _has_errors = bool_of_postcard ctx st in
    let* () = ensure_eof st in
    let type_decls = TypeDeclId.map_of_indexed_list crate.type_decls in
    let fun_decls = FunDeclId.map_of_indexed_list crate.fun_decls in
    let global_decls = GlobalDeclId.map_of_indexed_list crate.global_decls in
    let trait_decls = TraitDeclId.map_of_indexed_list crate.trait_decls in
    let trait_impls = TraitImplId.map_of_indexed_list crate.trait_impls in
    Ok
      ({
         name = crate.crate_name;
         options = crate.options;
         target_information = crate.target_information;
         declarations = Option.value ~default:[] crate.ordered_decls;
         type_decls;
         fun_decls;
         global_decls;
         trait_decls;
         trait_impls;
         unit_metadata = Option.get crate.unit_metadata;
       } : GAst.crate)
