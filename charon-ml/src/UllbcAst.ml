include GAst
open Types
open Values
open Expressions
open Meta
open Identifiers
module BlockId = IdGen ()

(** We define this type to control the name of the visitor functions
    (see e.g., {!UllbcAst.iter_statement_base} and {!switch}).
  *)
type block_id = BlockId.id [@@deriving show, ord]

(** Ancestor for {!UllbcAst.statement} iter visitor *)
class ['self] iter_statement_base =
  object (_self : 'self)
    inherit [_] GAst.iter_statement_base
    method visit_block_id : 'env -> block_id -> unit = fun _ _ -> ()
  end

(** Ancestor for {!UllbcAst.statement} map visitor *)
class ['self] map_statement_base =
  object (_self : 'self)
    inherit [_] GAst.map_statement_base
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
[@@deriving
  show,
    visitors
      {
        name = "iter_statement";
        variety = "iter";
        ancestors = [ "iter_statement_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_statement";
        variety = "map";
        ancestors = [ "map_statement_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

type switch =
  | If of block_id * block_id  (** Gives the `if` block and the `else` block *)
  | SwitchInt of integer_type * (scalar_value * block_id) list * block_id
      (** Gives the integer type, a map linking values to switch branches, and the
          otherwise block. Note that matches over enumerations are performed by
          switching over the discriminant, which is an integer.
       *)
[@@deriving
  show,
    visitors
      {
        name = "iter_switch";
        variety = "iter";
        ancestors = [ "iter_statement" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_switch";
        variety = "map";
        ancestors = [ "map_statement" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

(** A raw terminator: a terminator without meta data. *)
type raw_terminator =
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
[@@deriving
  show,
    visitors
      {
        name = "iter_terminator";
        variety = "iter";
        ancestors = [ "iter_switch" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_terminator";
        variety = "map";
        ancestors = [ "map_switch" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

type blocks = block list

and block = { statements : statement list; terminator : terminator }
[@@deriving show]

type expr_body = blocks gexpr_body [@@deriving show]
type fun_body = expr_body [@@deriving show]
type fun_decl = blocks gfun_decl [@@deriving show]
type global_body = expr_body [@@deriving show]
type global_decl = global_body option gglobal_decl [@@deriving show]

(** ULLBC crate *)
type crate = (blocks, global_body option) gcrate
