(** WARNING: this file is partially auto-generated. Do not edit `src/Expressions.ml`
    by hand. Edit `templaces/Expressions.ml` instead, or improve the code
    generation tool so avoid the need for hand-writing things.

    `templaces/Expressions.ml` contains the manual definitions and some `(*
    __REPLACEn__ *)` comments. These comments are replaced by auto-generated
    definitions by running `make generate-ml` in the crate root. The
    code-generation code is in `charon/src/bin/generate-ml`.
 *)
open Identifiers
open Types
open Values
module VarId = IdGen ()
module GlobalDeclId = Types.GlobalDeclId
module FunDeclId = Types.FunDeclId

(** We define this type to control the name of the visitor functions
    (see e.g., {!Charon.UllbcAst.iter_statement_base}).
  *)
type var_id = VarId.id [@@deriving show, ord]

type __expressions_0 = unit (* to start the recursive group *)
(* __REPLACE0__ *)
[@@deriving show, ord]

(** Ancestor the field_proj_kind iter visitor *)
class ['self] iter_place_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter
    method visit_type_decl_id : 'env -> type_decl_id -> unit = fun _ _ -> ()
    method visit_var_id : 'env -> var_id -> unit = fun _ _ -> ()
    method visit_variant_id : 'env -> variant_id -> unit = fun _ _ -> ()
    method visit_field_id : 'env -> field_id -> unit = fun _ _ -> ()
  end

(** Ancestor the field_proj_kind map visitor *)
class ['self] map_place_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.map

    method visit_type_decl_id : 'env -> type_decl_id -> type_decl_id =
      fun _ x -> x

    method visit_var_id : 'env -> var_id -> var_id = fun _ x -> x
    method visit_variant_id : 'env -> variant_id -> variant_id = fun _ x -> x
    method visit_field_id : 'env -> field_id -> field_id = fun _ x -> x
  end

type __expressions_1 = unit (* to start the recursive group *)
(* __REPLACE1__ *)
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_place";
        variety = "iter";
        ancestors = [ "iter_place_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_place";
        variety = "map";
        ancestors = [ "map_place_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

type __expressions_2 = unit (* to start the recursive group *)
(* __REPLACE2__ *)
[@@deriving show, ord]

let all_binops =
  [
    BitXor;
    BitAnd;
    BitOr;
    Eq;
    Lt;
    Le;
    Ne;
    Ge;
    Gt;
    Div;
    Rem;
    Add;
    Sub;
    Mul;
    Shl;
    Shr;
  ]

(** Ancestor for the constant_expr iter visitor *)
class ['self] iter_constant_expr_base =
  object (_self : 'self)
    inherit [_] iter_place
    inherit! [_] iter_ty
    method visit_assumed_fun_id : 'env -> assumed_fun_id -> unit = fun _ _ -> ()
  end

(** Ancestor the constant_expr map visitor *)
class ['self] map_constant_expr_base =
  object (_self : 'self)
    inherit [_] map_place
    inherit! [_] map_ty

    method visit_assumed_fun_id : 'env -> assumed_fun_id -> assumed_fun_id =
      fun _ x -> x
  end

type __expressions_3 = unit (* to start the recursive group *)
(* __REPLACE3__ *)
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_constant_expr";
        variety = "iter";
        ancestors = [ "iter_constant_expr_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_constant_expr";
        variety = "map";
        ancestors = [ "map_constant_expr_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

(** Ancestor the operand iter visitor *)
class ['self] iter_rvalue_base =
  object (_self : 'self)
    inherit [_] iter_constant_expr
    method visit_binop : 'env -> binop -> unit = fun _ _ -> ()
    method visit_borrow_kind : 'env -> borrow_kind -> unit = fun _ _ -> ()
  end

(** Ancestor the operand map visitor *)
class ['self] map_rvalue_base =
  object (_self : 'self)
    inherit [_] map_constant_expr
    method visit_binop : 'env -> binop -> binop = fun _ x -> x
    method visit_borrow_kind : 'env -> borrow_kind -> borrow_kind = fun _ x -> x
  end

type __expressions_4 = unit (* to start the recursive group *)
(* __REPLACE4__ *)
[@@deriving
  show,
    visitors
      {
        name = "iter_rvalue";
        variety = "iter";
        ancestors = [ "iter_rvalue_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_rvalue";
        variety = "map";
        ancestors = [ "map_rvalue_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]
