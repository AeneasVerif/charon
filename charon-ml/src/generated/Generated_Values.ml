(** The primitive values. *)
include BigInt

include Uchar

(** A char value *)
type char_value = (Uchar.t[@visitors.opaque]) [@@deriving show, eq, ord]

(* Ancestors for the literal visitors *)
class ['self] iter_literal_base =
  object (self : 'self)
    inherit [_] iter_big_int
    method visit_char_value : 'env -> char_value -> unit = fun _ _ -> ()
  end

class ['self] map_literal_base =
  object (self : 'self)
    inherit [_] map_big_int
    method visit_char_value : 'env -> char_value -> char_value = fun _ x -> x
  end

class virtual ['self] reduce_literal_base =
  object (self : 'self)
    inherit [_] reduce_big_int
    method visit_char_value : 'env -> char_value -> 'a = fun _ _ -> self#zero
  end

class virtual ['self] mapreduce_literal_base =
  object (self : 'self)
    inherit [_] mapreduce_big_int

    method visit_char_value : 'env -> char_value -> char_value * 'a =
      fun _ x -> (x, self#zero)
  end

type float_type = F16 | F32 | F64 | F128

(** This is simlar to the Scalar value above. However, instead of storing the
    float value itself, we store its String representation. This allows to
    derive the Eq and Ord traits, which are not implemented for floats *)
and float_value = { float_value : string; float_ty : float_type }

and int_ty = Isize | I8 | I16 | I32 | I64 | I128
and integer_type = Signed of int_ty | Unsigned of u_int_ty

(** A primitive value.

    Those are for instance used for the constant operands
    [crate::expressions::Operand::Const] *)
and literal =
  | VScalar of scalar_value
  | VFloat of float_value
  | VBool of bool
  | VChar of char_value
  | VByteStr of int list
  | VStr of string

(** Types of primitive values. Either an integer, bool, char *)
and literal_type =
  | TInt of int_ty
  | TUInt of u_int_ty
  | TFloat of float_type
  | TBool
  | TChar

(** A scalar value. *)
and scalar_value =
  | UnsignedScalar of u_int_ty * big_int
  | SignedScalar of int_ty * big_int

and u_int_ty = Usize | U8 | U16 | U32 | U64 | U128
[@@deriving
  show,
  eq,
  ord,
  visitors
    {
      name = "iter_literal";
      monomorphic = [ "env" ];
      variety = "iter";
      ancestors = [ "iter_literal_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_literal";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_literal_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "reduce_literal";
      monomorphic = [ "env" ];
      variety = "reduce";
      ancestors = [ "reduce_literal_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "mapreduce_literal";
      monomorphic = [ "env" ];
      variety = "mapreduce";
      ancestors = [ "mapreduce_literal_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]
