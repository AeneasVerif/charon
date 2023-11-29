(* TODO: this duplicates PrimitiveValues *)
type big_int = Z.t

let pp_big_int (fmt : Format.formatter) (bi : big_int) : unit =
  Format.pp_print_string fmt (Z.to_string bi)

let compare_big_int (bi0 : big_int) (bi1 : big_int) : int = Z.compare bi0 bi1
let show_big_int (bi : big_int) : string = Z.to_string bi

type var = VarName of string | VarIndex of int [@@deriving show, ord]

type literal = LInt of big_int | LBool of bool | LChar of char
[@@deriving show, ord]

(*type const_generic = CgVar of const_generic_var option | CgValue of Z.t*)
type ref_kind = RMut | RShared [@@deriving show, ord]
type region = RVar of var option | RStatic [@@deriving show, ord]
type primitive_adt = TTuple | TArray | TSlice [@@deriving show, ord]

type pattern = pattern_elem list
and pattern_elem = PIdent of string * generic_args | PImpl of expr

(** An expression can be a type or a trait ref.

    Note that we put in separate cases the tuple, array, slice and reference
    types because they have special syntax.
 *)
and expr =
  | EComp of pattern
      (** Compound expression: instantiated adt, primitive type, constant, etc.
          Note that if a type has generic arguments, they will be grouped with
          the last pattern elem.
       *)
  | EPrimAdt of primitive_adt * generic_args
  | ERef of region * expr * ref_kind
  | EVar of var option

and generic_arg = GExpr of expr | GValue of literal | GRegion of region
and generic_args = generic_arg list [@@deriving show, ord]
