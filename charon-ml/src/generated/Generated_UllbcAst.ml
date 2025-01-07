open Types
open Values
open Expressions
open Meta
open Identifiers
open GAst
module BlockId = IdGen ()

(** We define this type to control the name of the visitor functions
    (see e.g., {!UllbcAst.iter_statement_base} and {!switch}).
  *)
type block_id = BlockId.id [@@deriving show, ord]

(* Ancestors for the statement visitors *)
class ['self] iter_statement_base =
  object (self : 'self)
    inherit [_] iter_trait_impl
    method visit_block_id : 'env -> block_id -> unit = fun _ _ -> ()
  end

class ['self] map_statement_base =
  object (self : 'self)
    inherit [_] map_trait_impl
    method visit_block_id : 'env -> block_id -> block_id = fun _ x -> x
  end

(** A raw statement: a statement without meta data. *)
type raw_statement =
  | Assign of place * rvalue
  | Call of call
      (** A call. For now, we don't support dynamic calls (i.e. to a function pointer in memory). *)
  | FakeRead of place
  | SetDiscriminant of place * variant_id
  | StorageDead of var_id
      (** We translate this to [crate::llbc_ast::RawStatement::Drop] in LLBC *)
  | Deinit of place
      (** We translate this to [crate::llbc_ast::RawStatement::Drop] in LLBC *)
  | Drop of place
  | Assert of assertion
      (** A built-in assert, which corresponds to runtime checks that we remove, namely: bounds
          checks, over/underflow checks, div/rem by zero checks, pointer alignement check.
       *)
  | Nop  (** Does nothing. Useful for passes. *)

and statement = { span : span; content : raw_statement }

and switch =
  | If of block_id * block_id  (** Gives the `if` block and the `else` block *)
  | SwitchInt of integer_type * (scalar_value * block_id) list * block_id
      (** Gives the integer type, a map linking values to switch branches, and the
          otherwise block. Note that matches over enumerations are performed by
          switching over the discriminant, which is an integer.
       *)
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_statement";
        monomorphic = [ "env" ];
        variety = "iter";
        ancestors = [ "iter_statement_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_statement";
        monomorphic = [ "env" ];
        variety = "map";
        ancestors = [ "map_statement_base" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]

type blocks = block list

(** A raw terminator: a terminator without meta data. *)
and raw_terminator =
  | Goto of block_id  (** 
          Fields:
          - [target]
       *)
  | Switch of operand * switch
      (** 
          Fields:
          - [discr]
          - [targets]
       *)
  | Abort of abort_kind  (** Handles panics and impossible cases. *)
  | Return

and terminator = { span : span; content : raw_terminator }

and block = { statements : statement list; terminator : terminator }
[@@deriving
  show,
    ord,
    visitors
      {
        name = "iter_ullbc_ast";
        monomorphic = [ "env" ];
        variety = "iter";
        ancestors = [ "iter_statement" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      },
    visitors
      {
        name = "map_ullbc_ast";
        monomorphic = [ "env" ];
        variety = "map";
        ancestors = [ "map_statement" ];
        nude = true (* Don't inherit VisitorsRuntime *);
      }]
