(** Functions to load LLBC ASTs from json.

    See the comments for {!Charon.GAstOfJson} *)

open OfJsonBasic
open Types
open LlbcAst
include GAstOfJson
include Generated_LlbcOfJson

let expr_body_of_json (ctx : of_json_ctx) (js : json) :
    (fun_body, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Structured", body) ] ->
        let* body = gexpr_body_of_json block_of_json ctx body in
        Ok (Body body)
    | `Assoc [ ("Unstructured", _) ] ->
        (* Some .llbc bodies are emitted in ULLBC mode (e.g. UNIT_METADATA). *)
        Ok Opaque
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
