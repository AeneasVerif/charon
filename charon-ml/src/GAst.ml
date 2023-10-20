(** Definitions shared between the ULLBC and the LLBC ASTs. *)

open Names
open Types
open PrimitiveValues
open Meta
open Expressions
module FunDeclId = Expressions.FunDeclId
module GlobalDeclId = Expressions.GlobalDeclId
module TraitDeclId = Types.TraitDeclId
module TraitImplId = Types.TraitImplId
module TraitClauseId = Types.TraitClauseId

type fun_decl_id = FunDeclId.id [@@deriving show, ord]
type assumed_fun_id = Expressions.assumed_fun_id [@@deriving show, ord]
type fun_id = Expressions.fun_id [@@deriving show, ord]

type fun_id_or_trait_method_ref = Expressions.fun_id_or_trait_method_ref
[@@deriving show, ord]

(** A variable, as used in a function definition *)
type var = {
  index : VarId.id;  (** Unique variable identifier *)
  name : string option;
  var_ty : ety;
      (** The variable type - erased type, because variables are not used
       ** in function signatures: they are only used to declare the list of
       ** variables manipulated by a function body *)
}
[@@deriving show]

(** Ancestor the AST iter visitors *)
class ['self] iter_ast_base =
  object (_self : 'self)
    inherit [_] iter_rvalue
    inherit! [_] iter_literal

    (* Remark: can't inherit iter_literal_type because of a name collision (`Bool`) *)

    method visit_meta : 'env -> meta -> unit = fun _ _ -> ()
    method visit_integer_type : 'env -> integer_type -> unit = fun _ _ -> ()
  end

(** Ancestor the AST map visitors *)
class ['self] map_ast_base =
  object (_self : 'self)
    inherit [_] map_rvalue
    inherit! [_] map_literal

    (* Remark: can't inherit map_literal_type because of a name collision (`Bool`) *)

    method visit_meta : 'env -> meta -> meta = fun _ x -> x

    method visit_integer_type : 'env -> integer_type -> integer_type =
      fun _ x -> x
  end

(* Below: the types need not be mutually recursive, but it makes it easier
   to derive the visitors *)
type assertion = { cond : operand; expected : bool }

and call = { func : fn_ptr; args : operand list; dest : place }
[@@deriving
  show,
    visitors
      {
        name = "iter_call";
        variety = "iter";
        ancestors = [ "iter_ast_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_call";
        variety = "map";
        ancestors = [ "map_ast_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

(** Ancestor the {!LlbcAst.statement} and {!Charon.UllbcAst.statement} iter visitors *)
class ['self] iter_statement_base =
  object (_self : 'self)
    inherit [_] iter_call
  end

(** Ancestor the {!LlbcAst.statement} and {!Charon.UllbcAst.statement} map visitors *)
class ['self] map_statement_base =
  object (_self : 'self)
    inherit [_] map_call
  end

type params_info = {
  num_region_params : int;
  num_type_params : int;
  num_const_generic_params : int;
  num_trait_clauses : int;
  num_regions_outlive : int;
  num_types_outlive : int;
  num_trait_type_constraints : int;
}
[@@deriving show]

(** A function signature for function declarations *)
type fun_sig = {
  generics : generic_params;
  preds : predicates;
  parent_params_info : params_info option;
  inputs : sty list;
  output : sty;
  regions_hierarchy : region_var_groups;
}
[@@deriving show]

type fun_kind =
  | RegularKind  (** A "normal" function *)
  | TraitMethodImpl of trait_impl_id * trait_decl_id * string * bool
      (** Trait method implementation.

          Fields:
          - [trait impl id]
          - [trait_id]
          - [method_name]
          - [provided]: true if this function re-implements a provided method
        *)
  | TraitMethodDecl of trait_decl_id * string  (** A trait method declaration *)
  | TraitMethodProvided of trait_decl_id * string
      (** Trait method provided function (trait method declaration which defines a
          default implementation at the same time *)
[@@deriving show]

type 'body gexpr_body = {
  meta : meta;
  arg_count : int;
  locals : var list;
      (** The locals can be indexed with {!Expressions.VarId.id}.

          See {!Identifiers.Id.mapi} for instance.
       *)
  body : 'body;
}
[@@deriving show]

type 'body gfun_decl = {
  def_id : FunDeclId.id;
  meta : meta;
  name : fun_name;
  signature : fun_sig;
  kind : fun_kind;
  body : 'body gexpr_body option;
  is_global_decl_body : bool;
}
[@@deriving show]

type trait_decl = {
  def_id : trait_decl_id;
  name : name;
  generics : generic_params;
  preds : predicates;
  all_trait_clauses : trait_clause list;
  consts : (trait_item_name * (ety * global_decl_id option)) list;
  types : (trait_item_name * (trait_clause list * ety option)) list;
  required_methods : (trait_item_name * fun_decl_id) list;
  provided_methods : (trait_item_name * fun_decl_id option) list;
}
[@@deriving show]

type trait_impl = {
  def_id : trait_impl_id;
  name : name;
  impl_trait : strait_decl_ref;
  generics : generic_params;
  preds : predicates;
  consts : (trait_item_name * (ety * global_decl_id)) list;
  types : (trait_item_name * (etrait_ref list * ety)) list;
  required_methods : (trait_item_name * fun_decl_id) list;
  provided_methods : (trait_item_name * fun_decl_id) list;
}
[@@deriving show]

type 'id g_declaration_group = NonRec of 'id | Rec of 'id list
[@@deriving show]

type type_declaration_group = TypeDeclId.id g_declaration_group
[@@deriving show]

type fun_declaration_group = FunDeclId.id g_declaration_group [@@deriving show]

(** Module declaration. Globals cannot be mutually recursive. *)
type declaration_group =
  | Type of type_declaration_group
  | Fun of fun_declaration_group
  | Global of GlobalDeclId.id
  | TraitDecl of TraitDeclId.id
  | TraitImpl of TraitImplId.id
[@@deriving show]

(** A crate *)
type ('fun_decl, 'global_decl) gcrate = {
  name : string;
  declarations : declaration_group list;
  types : type_decl TypeDeclId.Map.t;
  functions : 'fun_decl FunDeclId.Map.t;
  globals : 'global_decl GlobalDeclId.Map.t;
  trait_decls : trait_decl TraitDeclId.Map.t;
  trait_impls : trait_impl TraitImplId.Map.t;
}
[@@deriving show]
