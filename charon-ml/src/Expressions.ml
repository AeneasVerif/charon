open Identifiers
open Types
open PrimitiveValues
module VarId = IdGen ()
module GlobalDeclId = Types.GlobalDeclId
module FunDeclId = IdGen ()

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
  | SliceLen
  | SliceIndexShared
  | SliceIndexMut
[@@deriving show, ord]

(** Ancestor the field_proj_kind iter visitor *)
class ['self] iter_field_proj_kind_base =
  object (_self : 'self)
    inherit [_] VisitorsRuntime.iter
    method visit_type_decl_id : 'env -> type_decl_id -> unit = fun _ _ -> ()
    method visit_var_id : 'env -> var_id -> unit = fun _ _ -> ()
    method visit_variant_id : 'env -> variant_id -> unit = fun _ _ -> ()
    method visit_field_id : 'env -> field_id -> unit = fun _ _ -> ()
  end

(** Ancestor the field_proj_kind map visitor *)
class ['self] map_field_proj_kind_base =
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
  | ProjOption of variant_id
      (** Option is an assumed type, coming from the standard library *)
  | ProjTuple of int  (** The integer gives the arity of the tuple *)
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_field_proj_kind";
        variety = "iter";
        ancestors = [ "iter_field_proj_kind_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_field_proj_kind";
        variety = "map";
        ancestors = [ "map_field_proj_kind_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

(* Remark: no `Index` variant, as it is eliminated by a micro-pass *)
type projection_elem = Deref | DerefBox | Field of field_proj_kind * field_id
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_projection_elem";
        variety = "iter";
        ancestors = [ "iter_field_proj_kind" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_projection_elem";
        variety = "map";
        ancestors = [ "map_field_proj_kind" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

type projection = projection_elem list
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_projection";
        variety = "iter";
        ancestors = [ "iter_projection_elem" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_projection";
        variety = "map";
        ancestors = [ "map_projection_elem" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

(** Ancestor the place iter visitor *)
class ['self] iter_place_base =
  object (_self : 'self)
    inherit [_] iter_projection
  end

(** Ancestor the place map visitor *)
class ['self] map_place_base =
  object (_self : 'self)
    inherit [_] map_projection
  end

type place = { var_id : var_id; projection : projection }
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

type borrow_kind = Shared | Mut | TwoPhaseMut | Shallow [@@deriving show]

(* TODO: FnPtr *)
type cast_kind = CastInteger of integer_type * integer_type
[@@deriving show, ord]

(* Remark: no `ArrayToSlice` variant: it gets eliminated in a micro-pass. *)
type unop =
  | Not
  | Neg
  | Cast of cast_kind
      (** Cast an integer from a source type to a target type *)
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
  object (self : 'self)
    inherit [_] iter_place
    inherit! [_] iter_ty
    method! visit_'r : 'env -> erased_region -> unit = self#visit_erased_region
    method visit_ety : 'env -> ety -> unit = self#visit_ty
    method visit_erased_region : 'env -> erased_region -> unit = fun _ _ -> ()

    method visit_egeneric_args : 'env -> egeneric_args -> unit =
      self#visit_generic_args

    method visit_etrait_ref : 'env -> etrait_ref -> unit = self#visit_trait_ref
    method visit_fun_decl_id : 'env -> fun_decl_id -> unit = fun _ _ -> ()
    method visit_assumed_fun_id : 'env -> assumed_fun_id -> unit = fun _ _ -> ()
  end

(** Ancestor the constant_expr map visitor *)
class ['self] map_constant_expr_base =
  object (self : 'self)
    inherit [_] map_place
    inherit! [_] map_ty

    method visit_'r : 'env -> erased_region -> erased_region =
      self#visit_erased_region

    method visit_ety : 'env -> ety -> ety = fun _ x -> x

    method visit_erased_region : 'env -> erased_region -> erased_region =
      fun _ x -> x

    method visit_egeneric_args : 'env -> egeneric_args -> egeneric_args =
      self#visit_generic_args

    method visit_etrait_ref : 'env -> etrait_ref -> etrait_ref =
      self#visit_trait_ref

    method visit_fun_decl_id : 'env -> fun_decl_id -> fun_decl_id = fun _ x -> x

    method visit_assumed_fun_id : 'env -> assumed_fun_id -> assumed_fun_id =
      fun _ x -> x
  end

type raw_constant_expr =
  | CLiteral of literal
  | CVar of const_generic_var_id
  | CTraitConst of etrait_ref * egeneric_args * string
  | CFnPtr of fn_ptr

and constant_expr = { value : raw_constant_expr; ty : ety }

and fn_ptr = {
  func : fun_id_or_trait_method_ref;
  generics : egeneric_args;
  trait_and_method_generic_args : egeneric_args option;
}

and fun_id_or_trait_method_ref =
  | FunId of fun_id
  | TraitMethod of etrait_ref * string * fun_decl_id
      (** The fun decl id is not really needed and here for convenience purposes *)

and fun_id = Regular of fun_decl_id | Assumed of assumed_fun_id
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
class ['self] iter_operand_base =
  object (_self : 'self)
    inherit [_] iter_constant_expr
  end

(** Ancestor the operand map visitor *)
class ['self] map_operand_base =
  object (_self : 'self)
    inherit [_] map_constant_expr
  end

type operand = Copy of place | Move of place | Constant of constant_expr
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_operand";
        variety = "iter";
        ancestors = [ "iter_operand_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_operand";
        variety = "map";
        ancestors = [ "map_operand_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

(** Ancestor the operand iter visitor *)
class ['self] iter_aggregate_kind_base =
  object (_self : 'self)
    inherit [_] iter_operand
  end

(** Ancestor the operand map visitor *)
class ['self] map_aggregate_kind_base =
  object (_self : 'self)
    inherit [_] map_operand
  end

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
type aggregate_kind =
  | AggregatedAdt of type_id * variant_id option * egeneric_args
  | AggregatedArray of ety * const_generic
[@@deriving
  show,
    visitors
      {
        name = "iter_aggregate_kind";
        variety = "iter";
        ancestors = [ "iter_aggregate_kind_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_aggregate_kind";
        variety = "map";
        ancestors = [ "map_aggregate_kind_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

(** Ancestor the rvalue iter visitor *)
class ['self] iter_rvalue_base =
  object (_self : 'self)
    inherit [_] iter_aggregate_kind
    method visit_unop : 'env -> unop -> unit = fun _ _ -> ()
    method visit_binop : 'env -> binop -> unit = fun _ _ -> ()
    method visit_borrow_kind : 'env -> borrow_kind -> unit = fun _ _ -> ()
  end

(** Ancestor the rvalue map visitor *)
class ['self] map_rvalue_base =
  object (_self : 'self)
    inherit [_] map_aggregate_kind
    method visit_unop : 'env -> unop -> unop = fun _ x -> x
    method visit_binop : 'env -> binop -> binop = fun _ x -> x
    method visit_borrow_kind : 'env -> borrow_kind -> borrow_kind = fun _ x -> x
  end

(* TODO: move the aggregate kind to operands *)
(* TODO: we should prefix the type variants with "T", this would avoid collisions *)
type rvalue =
  | Use of operand
  | RvRef of place * borrow_kind
  | UnaryOp of unop * operand
  | BinaryOp of binop * operand * operand
  | Discriminant of place
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
