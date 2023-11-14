open Types
open Expressions
open GAst

let option_to_string (to_string : 'a -> string) (x : 'a option) : string =
  match x with Some x -> "Some (" ^ to_string x ^ ")" | None -> "None"

let block_id_to_string (id : UllbcAst.BlockId.id) : string =
  "block@" ^ UllbcAst.BlockId.to_string id

let var_id_to_string (id : VarId.id) : string = "var@" ^ VarId.to_string id

let var_to_string (v : var) : string =
  match v.name with
  | None -> var_id_to_string v.index
  | Some name -> name ^ "^" ^ VarId.to_string v.index

type ('fun_body, 'global_body) fmt_env = {
  type_decls : type_decl TypeDeclId.Map.t;
  fun_decls : 'fun_body gfun_decl FunDeclId.Map.t;
  global_decls : 'global_body gglobal_decl GlobalDeclId.Map.t;
  trait_decls : trait_decl TraitDeclId.Map.t;
  trait_impls : trait_impl TraitImplId.Map.t;
  generics : generic_params;
  preds : predicates;
  locals : var list;
}
