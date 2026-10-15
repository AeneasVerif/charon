(** The primitive values. *)
include BigInt
include Uchar

(** A char value *)
type char_value = Uchar.t [@visitors.opaque] [@@deriving show, eq, ord]

let hash_char_value = Uchar.hash

(* __REPLACE0__ *)
