include GAstUtils
open Types
open LlbcAst
open Utils

(** Check if a {!type:LlbcAst.statement} contains loops *)
let statement_has_loops (st : statement) : bool =
  let obj =
    object
      inherit [_] iter_statement
      method! visit_Loop _ _ = raise Found
    end
  in
  try
    obj#visit_statement () st;
    false
  with Found -> true

(** Check if a {!type:LlbcAst.fun_decl} contains loops *)
let fun_decl_has_loops (fd : fun_decl) : bool =
  match fd.body with
  | Some body -> statement_has_loops body.body
  | None -> false

let compute_defs_maps (c : crate) :
    type_decl TypeDeclId.Map.t
    * fun_decl FunDeclId.Map.t
    * global_decl GlobalDeclId.Map.t =
  GAstUtils.compute_defs_maps (fun g -> g.def_id) c
