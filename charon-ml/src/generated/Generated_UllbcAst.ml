open Generated_Types
open Generated_Values
open Generated_Expressions
open Generated_Meta
open Generated_GAst
open Identifiers
module BlockId = IdGen ()

(** A "basic block", which contains a linear sequence of statements, followed by
    a terminator, which is where non-linear control-flow happens. *)
type block = {
  statements : statement list;
  terminator : terminator;
  kind : unwind_kind;
}

and block_id = (BlockId.id[@visitors.opaque])
and blocks = block list

(** A statement. *)
and statement = {
  span : span;
  kind : statement_kind;
  comments_before : string list;  (** Comments that precede this statement. *)
}

and statement_kind =
  | Assign of place * rvalue
  | SetDiscriminant of place * variant_id
      (** A call. For now, we don't support dynamic calls (i.e. to a function
          pointer in memory). *)
  | StorageLive of local_id
      (** Indicates that this local should be allocated; if it is already
          allocated, this frees the local and re-allocates it. The arguments do
          not receive a [StorageLive]. We ensure in the micro-pass
          [insert_storage_statements] that all other locals have a [StorageLive]
          associated with them. *)
  | StorageDead of local_id
      (** Deallocates the given local; if it is already deallocated, this is a
          no-op. Not all local deallocations are explicit: if a non-return local
          is still live at function end (return or unwind), it is implicitly
          deallocated. If [--deallocate-all-locals] is set, all local
          deallocations are made explicit. *)
  | PlaceMention of place
      (** A place is mentioned, but not accessed. The place itself must still be
          valid though, so this statement is not a no-op: it can trigger UB if
          the place's projections are not valid (e.g. because they go out of
          bounds). *)
  | Borrowck of borrowck_statement
      (** Statements that only affect borrow-checking. *)
  | Assert of assertion * abort_kind
      (** A non-diverging runtime check for a condition. This can be either:
          - Emitted for inlined "assumes" (which cause UB on failure)
          - Reconstructed from [if b { panic() }] if [--reconstruct-asserts] is
            set.

          This statement comes with the effect that happens when the check fails
          (rather than representing it as an unwinding edge).

          Fields:
          - [assert]
          - [on_failure] *)
  | Nop  (** Does nothing. Useful for passes. *)

(** A terminator: instruction to execute at the end of a block, which may jump
    to other blocks. *)
and terminator = {
  span : span;
  kind : terminator_kind;
  comments_before : string list;  (** Comments that precede this terminator. *)
}

and terminator_kind =
  | Goto of block_id
      (** Fields:
          - [target] *)
  | Switch of switch_data * block_id list
      (** Fields:
          - [data]
          - [branches] *)
  | Call of call * block_id * block_id
      (** Fields:
          - [call]
          - [target]
          - [on_unwind] *)
  | Drop of drop_kind * place * fn_ptr * block_id * block_id
      (** Drop the value at the given place.

          Depending on [DropKind], this may be a real call to [drop_glue], or a
          conditional call that should only happen if the place has not been
          moved out of. See the docs of [DropKind] for more details; to get
          precise drops use [--precise-drops].

          Fields:
          - [kind]
          - [place]
          - [fn_ptr]: Reference to the [drop_glue] code to call on drop.
          - [target]
          - [on_unwind] *)
  | InlineAsm of inline_asm * block_id option * block_id list * block_id
      (** An inline assembly block.

          Fields:
          - [asm]
          - [fallthrough]: Next block if the control-flow continues without
            jumping. Absent for [naked_asm!] and [noreturn].
          - [labels]: Targets of [[AsmOperand::Label]] operands.
          - [on_unwind]: Action to be taken if the inline assembly unwinds. *)
  | TAssert of assertion * block_id * block_id
      (** Assert that the given condition holds, and if not, unwind to the given
          block. This is used for bounds checks, overflow checks, etc.

          Fields:
          - [assert]
          - [target]
          - [on_unwind] *)
  | Panic of name * block_id
      (** Call to a built-in panicking function. Only if
          [--reconstruct-panic-calls] is passed.

          Fields:
          - [name]: The name of the function that was called.
          - [on_unwind] *)
  | UnwindTerminate
      (** Unwinding must stop for ABI reasons or because cleanup code panicked
          again. *)
  | UnwindResume  (** Unwind out of the current function into its caller. *)
  | Return
  | UndefinedBehavior
      (** Reaching this point is undefined behavior in the Rust abstract
          machine. *)

(** Where a block runs relative to unwinding. *)
and unwind_kind =
  | Regular  (** A non-unwind block; it may start unwinding. *)
  | Cleanup  (** An unwind block that may continue unwinding. *)
  | Terminate
      (** An unwind block that may only terminate the execution; used for
          double-unwinds or unwinding across incompatible ABI boundaries. *)
[@@deriving
  show,
  eq,
  ord,
  visitors
    {
      name = "iter_ullbc_ast";
      monomorphic = [ "env" ];
      variety = "iter";
      ancestors = [ "iter_trait_impl" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_ullbc_ast";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_trait_impl" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]

let rec hash_block : block -> int =
 fun (x : block) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 ((HashBasic.hash_list hash_statement) x.statements))
       (hash_terminator x.terminator))
    (hash_unwind_kind x.kind)

and hash_block_id : block_id -> int = fun (x : block_id) -> BlockId.hash_id x

and hash_blocks : blocks -> int =
 fun (x : blocks) -> (HashBasic.hash_list hash_block) x

and hash_statement : statement -> int =
 fun (x : statement) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 (hash_span x.span))
       (hash_statement_kind x.kind))
    ((HashBasic.hash_list HashBasic.hash_string) x.comments_before)

and hash_statement_kind : statement_kind -> int =
 fun (x : statement_kind) ->
  match x with
  | Assign (x0, x1) ->
      HashBasic.combine (HashBasic.combine 0 (hash_place x0)) (hash_rvalue x1)
  | SetDiscriminant (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 1 (hash_place x0))
        (hash_variant_id x1)
  | StorageLive x0 -> HashBasic.combine 2 (hash_local_id x0)
  | StorageDead x0 -> HashBasic.combine 3 (hash_local_id x0)
  | PlaceMention x0 -> HashBasic.combine 4 (hash_place x0)
  | Borrowck x0 -> HashBasic.combine 5 (hash_borrowck_statement x0)
  | Assert (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 6 (hash_assertion x0))
        (hash_abort_kind x1)
  | Nop -> 7

and hash_terminator : terminator -> int =
 fun (x : terminator) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 (hash_span x.span))
       (hash_terminator_kind x.kind))
    ((HashBasic.hash_list HashBasic.hash_string) x.comments_before)

and hash_terminator_kind : terminator_kind -> int =
 fun (x : terminator_kind) ->
  match x with
  | Goto x0 -> HashBasic.combine 0 (hash_block_id x0)
  | Switch (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 1 (hash_switch_data x0))
        ((HashBasic.hash_list hash_block_id) x1)
  | Call (x0, x1, x2) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine 2 (hash_call x0))
           (hash_block_id x1))
        (hash_block_id x2)
  | Drop (x0, x1, x2, x3, x4) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine
              (HashBasic.combine
                 (HashBasic.combine 3 (hash_drop_kind x0))
                 (hash_place x1))
              (hash_fn_ptr x2))
           (hash_block_id x3))
        (hash_block_id x4)
  | InlineAsm (x0, x1, x2, x3) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine
              (HashBasic.combine 4 (hash_inline_asm x0))
              ((HashBasic.hash_option hash_block_id) x1))
           ((HashBasic.hash_list hash_block_id) x2))
        (hash_block_id x3)
  | TAssert (x0, x1, x2) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine 5 (hash_assertion x0))
           (hash_block_id x1))
        (hash_block_id x2)
  | Panic (x0, x1) ->
      HashBasic.combine (HashBasic.combine 6 (hash_name x0)) (hash_block_id x1)
  | UnwindTerminate -> 7
  | UnwindResume -> 8
  | Return -> 9
  | UndefinedBehavior -> 10

and hash_unwind_kind : unwind_kind -> int =
 fun (x : unwind_kind) ->
  match x with
  | Regular -> 0
  | Cleanup -> 1
  | Terminate -> 2

(* __REPLACE1__ *)
