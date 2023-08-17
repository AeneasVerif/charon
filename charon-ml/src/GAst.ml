(** Definitions shared between the ULLBC and the LLBC ASTs. *)

open Identifiers
open Names
open Types
open PrimitiveValues
open Expressions
open Meta
module FunDeclId = IdGen ()
module GlobalDeclId = Expressions.GlobalDeclId

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

type assumed_fun_id =
  | Replace  (** [core::mem::replace] *)
  | BoxNew
  | BoxDeref  (** [core::ops::deref::Deref::<alloc::boxed::Box<T>>::deref] *)
  | BoxDerefMut
      (** [core::ops::deref::DerefMut::<alloc::boxed::Box<T>>::deref_mut] *)
  | BoxFree
  | VecNew
  | VecPush
  | VecInsert
  | VecLen
  | VecIndex  (** [core::ops::index::Index::index<alloc::vec::Vec<T>, usize>] *)
  | VecIndexMut
      (** [core::ops::index::IndexMut::index_mut<alloc::vec::Vec<T>, usize>] *)
  | ArrayIndexShared
  | ArrayIndexMut
  | ArrayToSliceShared
  | ArrayToSliceMut
  | ArraySubsliceShared
  | ArraySubsliceMut
  | SliceLen
  | SliceIndexShared
  | SliceIndexMut
  | SliceSubsliceShared
  | SliceSubsliceMut
[@@deriving show, ord]

type fun_id = Regular of FunDeclId.id | Assumed of assumed_fun_id
[@@deriving show, ord]

(** Ancestor the AST iter visitors *)
class ['self] iter_ast_base =
  object (_self : 'self)
    inherit [_] iter_rvalue
    inherit! [_] iter_literal
    (* Remark: can't inherit iter_literal_type because of a name collision (`Bool`) *)

    method visit_fun_id : 'env -> fun_id -> unit = fun _ _ -> ()
    method visit_meta : 'env -> meta -> unit = fun _ _ -> ()
    method visit_integer_type : 'env -> integer_type -> unit = fun _ _ -> ()
  end

(** Ancestor the AST map visitors *)
class ['self] map_ast_base =
  object (_self : 'self)
    inherit [_] map_rvalue
    inherit! [_] map_literal
    (* Remark: can't inherit map_literal_type because of a name collision (`Bool`) *)

    method visit_fun_id : 'env -> fun_id -> fun_id = fun _ x -> x
    method visit_meta : 'env -> meta -> meta = fun _ x -> x

    method visit_integer_type : 'env -> integer_type -> integer_type =
      fun _ x -> x
  end

type assertion = { cond : operand; expected : bool }
[@@deriving
  show,
    visitors
      {
        name = "iter_assertion";
        variety = "iter";
        ancestors = [ "iter_ast_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_assertion";
        variety = "map";
        ancestors = [ "map_ast_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

type call = {
  func : fun_id;
  region_args : erased_region list;
  type_args : ety list;
  const_generic_args : const_generic list;
  args : operand list;
  dest : place;
}
[@@deriving
  show,
    visitors
      {
        name = "iter_call";
        variety = "iter";
        ancestors = [ "iter_assertion" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_call";
        variety = "map";
        ancestors = [ "map_assertion" ];
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

(** A function signature, as used when declaring functions *)
type fun_sig = {
  region_params : region_var list;
  regions_hierarchy : region_var_groups;
  type_params : type_var list;
      (** The type parameters can be indexed with {!Types.TypeVarId.id}.

          See {!Identifiers.Id.mapi} for instance.
       *)
  const_generic_params : const_generic_var list;
      (** The const generic parameters can be indexed with {!Types.ConstGenericVarId.id}.

          See {!Identifiers.Id.mapi} for instance.
       *)
  inputs : sty list;
  output : sty;
}
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
  body : 'body gexpr_body option;
  is_global_decl_body : bool;
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
[@@deriving show]

(** A crate *)
type ('fun_decl, 'global_decl) gcrate = {
  name : string;
  declarations : declaration_group list;
  types : type_decl TypeDeclId.Map.t;
  functions : 'fun_decl FunDeclId.Map.t;
  globals : 'global_decl GlobalDeclId.Map.t;
}
[@@deriving show]
