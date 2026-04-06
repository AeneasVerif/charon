(** Functions to load ULLBC ASTs from json.

    See the comments for {!GAstOfJson} *)

open OfJsonBasic
open Types
open Expressions
open UllbcAst
include GAstOfJson
include Generated_UllbcOfJson

let expr_body_of_json (ctx : of_json_ctx) (js : json) :
    (fun_body, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Unstructured", body) ] ->
        let* body = gexpr_body_of_json (list_of_json block_of_json) ctx body in
        Ok (Body body)
    | `String "TraitMethodWithoutDefault" -> Ok TraitMethodWithoutDefault
    | `Assoc [ ("Extern", sym) ] ->
        let* sym = string_of_json ctx sym in
        Ok (Extern sym)
    | `Assoc [ ("Intrinsic", name) ] ->
        let* name = string_of_json ctx name in
        Ok (Intrinsic name)
    | `String "Opaque" -> Ok Opaque
    | `String "Missing" -> Ok Missing
    | `Assoc [ ("Error", e) ] ->
        let* e = error_of_json ctx e in
        Ok (GAst.Error e)
    | _ -> Error "")

let crate_of_json (js : json) : (crate, string) result =
  gcrate_of_json expr_body_of_json js
