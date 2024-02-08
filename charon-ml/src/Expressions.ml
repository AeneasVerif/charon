open Identifiers
open Types
open Values
module VarId = IdGen ()
module GlobalDeclId = Types.GlobalDeclId
module FunDeclId = Types.FunDeclId

type fun_decl_id = FunDeclId.id [@@deriving show, ord]

(** We define this type to control the name of the visitor functions
    (see e.g., {!Charon.UllbcAst.iter_statement_base}).
  *)
type var_id = VarId.id [@@deriving show, ord]

type assumed_fun_id =
  | BoxNew
  | BoxFree
  | ArrayIndexShared
  | ArrayIndexMut
  | ArrayToSliceShared
  | ArrayToSliceMut
  | ArrayRepeat
  | SliceIndexShared
  | SliceIndexMut
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

type field_proj_kind =
  | ProjAdt of type_decl_id * variant_id option
  | ProjTuple of int  (** The integer gives the arity of the tuple *)

(* Remark: no `Index` variant, as it is eliminated by a micro-pass *)
and projection_elem = Deref | DerefBox | Field of field_proj_kind * field_id
and projection = projection_elem list

and place = { var_id : var_id; projection : projection }
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

type borrow_kind = BShared | BMut | BTwoPhaseMut | BShallow
[@@deriving show, ord]

(** A binary operation

    Note that we merge checked binops and unchecked binops: we perform a
    micro-pass on the MIR AST to remove the assertions introduced by rustc,
    and later extract the binops which can fail (addition, substraction, etc.)
    or have preconditions (division, remainder...) to monadic functions.
 *)
type binop =
  | BitXor
  | BitAnd
  | BitOr
  | Eq
  | Lt
  | Le
  | Ne
  | Ge
  | Gt
  | Div
  | Rem
  | Add
  | Sub
  | Mul
  | Shl
  | Shr
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

type cast_kind =
  | CastScalar of literal_type * literal_type
  | CastFnPtr of ty * ty

(* Remark: no `ArrayToSlice` variant: it gets eliminated in a micro-pass. *)
and unop =
  | Not
  | Neg
  | Cast of cast_kind
      (** Cast an integer from a source type to a target type *)

and raw_constant_expr =
  | CLiteral of literal
  | CVar of const_generic_var_id
  | CTraitConst of trait_ref * string
  | CFnPtr of fn_ptr

and constant_expr = { value : raw_constant_expr; ty : ty }

and fn_ptr = {
  func : fun_id_or_trait_method_ref;
  generics : generic_args;
  trait_and_method_generic_args : generic_args option;
}

and fun_id_or_trait_method_ref =
  | FunId of fun_id
  | TraitMethod of trait_ref * string * fun_decl_id
      (** The fun decl id is not really needed and here for convenience purposes *)

(* TODO: prefix with "F" *)
and fun_id = FRegular of fun_decl_id | FAssumed of assumed_fun_id
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

type operand = Copy of place | Move of place | Constant of constant_expr

(** An aggregated ADT.

    Note that ADTs are desaggregated at some point in MIR. For instance, if
    we have in Rust:
    {[
      let ls = Cons(hd, tl);
    ]}

    In MIR we have (yes, the discriminant update happens *at the end* for some
    reason):
    {[
      (ls as Cons).0 = move hd;
      (ls as Cons).1 = move tl;
      discriminant(ls) = 0; // assuming [Cons] is the variant of index 0
    ]}

    Rem.: in the Aeneas semantics, both cases are handled (in case of desaggregated
    initialization, [ls] is initialized to [⊥], then this [⊥] is expanded to
    [Cons (⊥, ⊥)] upon the first assignment, at which point we can initialize
    the field 0, etc.).
 *)
and aggregate_kind =
  | AggregatedAdt of type_id * variant_id option * generic_args
  | AggregatedArray of ty * const_generic
  | AggregatedClosure of fun_decl_id * generic_args

(* TODO: move the aggregate kind to operands *)
(* TODO: we should prefix the type variants with "T", this would avoid collisions *)
and rvalue =
  | Use of operand
  | RvRef of place * borrow_kind
  | UnaryOp of unop * operand
  | BinaryOp of binop * operand * operand
  | Discriminant of place * type_decl_id
  | Aggregate of aggregate_kind * operand list
  | Global of global_decl_id
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
