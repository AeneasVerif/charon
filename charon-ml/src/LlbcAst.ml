include GAst
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
  (* FIXME: rename to `Abort` *)
  | Panic
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

and statement = { span : span; content : raw_statement }

and switch =
  | If of operand * statement * statement
      (** Gives the `if` block and the `else` block. The `Operand` is the condition of the `if`, e.g. `if (y == 0)` could become
          ```rust,ignore
          v@3 := copy y; // Represented as `Assign(v@3, Use(Copy(y))`
          v@2 := move v@3 == 0; // Represented as `Assign(v@2, BinOp(BinOp::Eq, Move(y), Const(0)))`
          if (move v@2) { // Represented as `If(Move(v@2), <then branch>, <else branch>)`
          ```
       *)
  | SwitchInt of
      operand * integer_type * (scalar_value list * statement) list * statement
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
  | Match of place * (variant_id list * statement) list * statement option
      (** A match over an ADT.

          The match statement is introduced in [crate::remove_read_discriminant]
          (whenever we find a discriminant read, we merge it with the subsequent
          switch into a match).
       *)
[@@deriving
  show,
    visitors
      {
        name = "iter_statement";
        variety = "iter";
        ancestors = [ "iter_statement_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_statement";
        variety = "map";
        ancestors = [ "map_statement_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]

type expr_body = statement gexpr_body [@@deriving show]
type fun_body = expr_body [@@deriving show]
type fun_decl = statement gfun_decl [@@deriving show]

(* TODO: the function id should be an option *)
type global_decl = FunDeclId.id gglobal_decl [@@deriving show]

(** LLBC crate *)
type crate = (statement, FunDeclId.id) gcrate
