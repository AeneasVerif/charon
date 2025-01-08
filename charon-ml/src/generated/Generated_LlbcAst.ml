open GAst
open Types
open Values
open Expressions
open Meta

(** A raw statement: a statement without meta data. *)
type raw_statement =
  | Assign of place * rvalue
  | FakeRead of place
  | SetDiscriminant of place * variant_id
  | Drop of place
  | Assert of assertion
  | Call of call
  | Abort of abort_kind
  | Return
  | Break of int
      (** Break to (outer) loop. The [int] identifies the loop to break to:
        * 0: break to the first outer loop (the current loop)
        * 1: break to the second outer loop
        * ...
        *)
  | Continue of int
      (** Continue to (outer) loop. The loop identifier works
        the same way as for {!Break} *)
  | Nop
  | Sequence of statement * statement
  | Switch of switch
  | Loop of statement
  | Error of string

and statement = {
  span : span;
  content : raw_statement;
  comments_before : string list;  (** Comments that precede this statement. *)
}

and block = statement

and switch =
  | If of operand * block * block
      (** Gives the `if` block and the `else` block. The `Operand` is the condition of the `if`, e.g. `if (y == 0)` could become
          ```rust,ignore
          v@3 := copy y; // Represented as `Assign(v@3, Use(Copy(y))`
          v@2 := move v@3 == 0; // Represented as `Assign(v@2, BinOp(BinOp::Eq, Move(y), Const(0)))`
          if (move v@2) { // Represented as `If(Move(v@2), <then branch>, <else branch>)`
          ```
       *)
  | SwitchInt of
      operand * integer_type * (scalar_value list * block) list * block
      (** Gives the integer type, a map linking values to switch branches, and the
          otherwise block. Note that matches over enumerations are performed by
          switching over the discriminant, which is an integer.
          Also, we use a `Vec` to make sure the order of the switch
          branches is preserved.

          Rk.: we use a vector of values, because some of the branches may
          be grouped together, like for the following code:
          ```text
          match e {
            E::V1 | E::V2 => ..., // Grouped
            E::V3 => ...
          }
          ```
       *)
  | Match of place * (variant_id list * block) list * block option
      (** A match over an ADT.

          The match statement is introduced in [crate::remove_read_discriminant]
          (whenever we find a discriminant read, we merge it with the subsequent
          switch into a match).
       *)
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_statement";
        monomorphic = [ "env" ];
        variety = "iter";
        ancestors = [ "iter_trait_impl" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_statement";
        monomorphic = [ "env" ];
        variety = "map";
        ancestors = [ "map_trait_impl" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]
