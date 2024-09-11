(** The primitive values. *)

(** We use big integers to store the integer values (this way we don't have
    to think about the bounds, nor architecture issues - Rust allows to
    manipulate 128-bit integers for instance).
 *)
type big_int = Z.t

let big_int_of_yojson (json : Yojson.Safe.t) : (big_int, string) result =
  match json with
  | `Int i -> Ok (Z.of_int i)
  | `Intlit is -> Ok (Z.of_string is)
  | _ -> Error "not an integer or an integer literal"

let big_int_to_yojson (i : big_int) = `Intlit (Z.to_string i)

let pp_big_int (fmt : Format.formatter) (bi : big_int) : unit =
  Format.pp_print_string fmt (Z.to_string bi)

let compare_big_int (bi0 : big_int) (bi1 : big_int) : int = Z.compare bi0 bi1
let show_big_int (bi : big_int) : string = Z.to_string bi

(* Ancestors for the literal visitors *)
class ['self] iter_literal_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.iter
    method visit_big_int : 'env -> big_int -> unit = fun _ _ -> ()
  end

class ['self] map_literal_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.map
    method visit_big_int : 'env -> big_int -> big_int = fun _ x -> x
  end

class virtual ['self] reduce_literal_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.reduce
    method visit_big_int : 'env -> big_int -> 'a = fun _ _ -> self#zero
  end

class virtual ['self] mapreduce_literal_base =
  object (self : 'self)
    inherit [_] VisitorsRuntime.mapreduce

    method visit_big_int : 'env -> big_int -> big_int * 'a =
      fun _ x -> (x, self#zero)
  end

type integer_type =
  | Isize
  | I8
  | I16
  | I32
  | I64
  | I128
  | Usize
  | U8
  | U16
  | U32
  | U64
  | U128

and float_type = F16 | F32 | F64 | F128

(** Types of primitive values. Either an integer, bool, char *)
and literal_type =
  | TInteger of integer_type
  | TFloat of float_type
  | TBool
  | TChar

(** A primitive value.

    Those are for instance used for the constant operands [crate::expressions::Operand::Const]
 *)
and literal =
  | VScalar of scalar_value
  | VFloat of float_value
  | VBool of bool
  | VChar of char
  | VByteStr of int list
  | VStr of string

(** A scalar value. *)
and scalar_value = {
  (* Note that we use unbounded integers everywhere.
     We then harcode the boundaries for the different types.
  *)
  value : big_int;
  int_ty : integer_type;
}

(** This is simlar to the Scalar value above. However, instead of storing
    the float value itself, we store its String representation. This allows
    to derive the Eq and Ord traits, which are not implemented for floats
 *)
and float_value = { float_value : string; float_ty : float_type }
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_literal";
        variety = "iter";
        ancestors = [ "iter_literal_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_literal";
        variety = "map";
        ancestors = [ "map_literal_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "reduce_literal";
        variety = "reduce";
        ancestors = [ "reduce_literal_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "mapreduce_literal";
        variety = "mapreduce";
        ancestors = [ "mapreduce_literal_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]
