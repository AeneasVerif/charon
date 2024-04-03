(** Definitions shared between the ULLBC and the LLBC ASTs. *)
open Types

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
  var_ty : ty;
      (** The variable type - erased type, because variables are not used
       ** in function signatures: they are only used to declare the list of
       ** variables manipulated by a function body *)
}
[@@deriving show]

(** Ancestor the AST iter visitors *)
class ['self] iter_ast_base =
  object (_self : 'self)
    inherit [_] iter_rvalue
    inherit! [_] iter_predicates
  end

(** Ancestor the AST map visitors *)
class ['self] map_ast_base =
  object (_self : 'self)
    inherit [_] map_rvalue
    inherit! [_] map_predicates
  end

(* Below: the types need not be mutually recursive, but it makes it easier
   to derive the visitors *)
type assertion = { cond : operand; expected : bool }
and fn_operand = FnOpRegular of fn_ptr | FnOpMove of place

and call = { func : fn_operand; args : operand list; dest : place }
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

type closure_kind = Fn | FnMut | FnOnce [@@deriving show]
type closure_info = { kind : closure_kind; state : ty list } [@@deriving show]

(** A function signature for function declarations *)
type fun_sig = {
  is_unsafe : bool;
  is_closure : bool;
  closure_info : closure_info option;
  generics : generic_params;
  preds : predicates;
  parent_params_info : params_info option;
  inputs : ty list;
  output : ty;
}
[@@deriving show]

type item_kind =
  | RegularKind
      (** A "normal" item (either defined at the top-level, or inside
          a type impl block). *)
  | TraitItemImpl of trait_impl_id * trait_decl_id * string * bool
      (** Trait item implementation.

          Fields:
          - [trait impl id]
          - [trait_id]
          - [item_name]
          - [provided]: true if this item *re-implements* a provided item
        *)
  | TraitItemDecl of trait_decl_id * string  (** A trait item declaration *)
  | TraitItemProvided of trait_decl_id * string
      (** Provided trait item (trait item declaration which defines a
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
  is_local : bool;
  attributes : string list;
  name : name;
  signature : fun_sig;
  kind : item_kind;
  body : 'body gexpr_body option;
  is_global_decl_body : bool;
}
[@@deriving show]

type trait_decl = {
  def_id : trait_decl_id;
  meta : meta;
  is_local : bool;
  attributes : string list;
  name : name;
  generics : generic_params;
  preds : predicates;
  parent_clauses : trait_clause list;
  consts : (trait_item_name * (ty * global_decl_id option)) list;
  types : (trait_item_name * (trait_clause list * ty option)) list;
  required_methods : (trait_item_name * fun_decl_id) list;
  provided_methods : (trait_item_name * fun_decl_id option) list;
}
[@@deriving show]

type trait_impl = {
  def_id : trait_impl_id;
  meta : meta;
  is_local : bool;
  attributes : string list;
  name : name;
  impl_trait : trait_decl_ref;
  generics : generic_params;
  preds : predicates;
  parent_trait_refs : trait_ref list;
  consts : (trait_item_name * (ty * global_decl_id)) list;
  types : (trait_item_name * (trait_ref list * ty)) list;
  required_methods : (trait_item_name * fun_decl_id) list;
  provided_methods : (trait_item_name * fun_decl_id) list;
}
[@@deriving show]

type 'id g_declaration_group = NonRecGroup of 'id | RecGroup of 'id list
[@@deriving show]

type type_declaration_group = TypeDeclId.id g_declaration_group
[@@deriving show]

type fun_declaration_group = FunDeclId.id g_declaration_group [@@deriving show]

(** Module declaration. Globals cannot be mutually recursive. *)
type declaration_group =
  | TypeGroup of type_declaration_group
  | FunGroup of fun_declaration_group
  | GlobalGroup of GlobalDeclId.id
  | TraitDeclGroup of TraitDeclId.id
  | TraitImplGroup of TraitImplId.id
[@@deriving show]

type 'body gglobal_decl = {
  def_id : GlobalDeclId.id;
  meta : meta;
  is_local : bool;
  attributes : string list;
  name : name;
  generics : generic_params;
  preds : predicates;
  ty : ty;
  kind : item_kind;
  body : 'body;
}
[@@deriving show]

(** A crate *)
type ('fun_body, 'global_body) gcrate = {
  name : string;
  declarations : declaration_group list;
  type_decls : type_decl TypeDeclId.Map.t;
  fun_decls : 'fun_body gfun_decl FunDeclId.Map.t;
  global_decls : 'global_body gglobal_decl GlobalDeclId.Map.t;
  trait_decls : trait_decl TraitDeclId.Map.t;
  trait_impls : trait_impl TraitImplId.Map.t;
}
[@@deriving show]
