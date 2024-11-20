(** Functions to load ULLBC ASTs from json.

    See the comments for {!GAstOfJson}
 *)

include GAstOfJson
open OfJsonBasic
open Types
open Expressions
open UllbcAst

(* __REPLACE0__ *)

let expr_body_of_json (ctx : of_json_ctx) (js : json) :
    (expr_body, string) result =
  combine_error_msgs js __FUNCTION__
    (match js with
    | `Assoc [ ("Unstructured", body) ] ->
        let* body =
          gexpr_body_of_json (blocks_of_json ctx) ctx body
        in
        Ok body
    | _ -> Error "")

let crate_of_json (js : json) : (crate, string) result =
  gcrate_of_json expr_body_of_json js
