open Types
open Expressions
open GAst

let option_to_string (to_string : 'a -> string) (x : 'a option) : string =
  match x with Some x -> "Some (" ^ to_string x ^ ")" | None -> "None"

let block_id_to_string (id : UllbcAst.BlockId.id) : string =
  "block@" ^ UllbcAst.BlockId.to_string id

(** The formatting environment can be incomplete: if some information is missing
    (for instance we can't find the type variable for a given index) we print
    the id in raw format. *)
type ('fun_body, 'global_body) fmt_env = {
  type_decls : type_decl TypeDeclId.Map.t;
  fun_decls : 'fun_body gfun_decl FunDeclId.Map.t;
  global_decls : 'global_body gglobal_decl GlobalDeclId.Map.t;
  trait_decls : trait_decl TraitDeclId.Map.t;
  trait_impls : trait_impl TraitImplId.Map.t;
  regions : region_var list list;
      (** We have a stack of regions, because we can dive into groups of
          universally quantified regions (for instance because of the arrow
          type).

          Note that the variables in the generics don't need to be ordered following their
          indices, i.e., the region var of index 0 doesn't have to be at index 0,
          etc. We lookup the variables by checking their id, not their position.
      *)
  types : type_var list;
  const_generics : const_generic_var list;
  trait_clauses : trait_clause list;
  preds : predicates;
  locals : (VarId.id * string option) list;
      (** The local variables don't need to be ordered (same as the generics) *)
}

let fmt_env_update_generics_and_preds (env : ('a, 'b) fmt_env)
    (generics : generic_params) (preds : predicates) : ('a, 'b) fmt_env =
  let { regions; types; const_generics; trait_clauses } : generic_params =
    generics
  in
  {
    env with
    regions = regions :: env.regions;
    types;
    const_generics;
    trait_clauses;
    preds;
  }

let fmt_env_push_regions (env : ('a, 'b) fmt_env) (regions : region_var list) :
    ('a, 'b) fmt_env =
  { env with regions = regions :: env.regions }
