open Generated_GAst
open Generated_Types
open Generated_Values
open Generated_Expressions
open Generated_Meta
open Identifiers
module StatementId = IdGen ()
module BlockId = IdGen ()

(** A sequence of statements. *)
type block = {
  span : span;
  block_id : block_id;  (** An integer uniquely identifying this block. *)
  statements : statement list;
}

and block_id = (BlockId.id[@visitors.opaque])

(** A statement, which can contain nested statements inside loops or switchers.
*)
and statement = {
  span : span;
  statement_id : statement_id;
      (** An integer uniquely identifying this statement. *)
  kind : statement_kind;
  comments_before : string list;  (** Comments that precede this statement. *)
}

and statement_id = (StatementId.id[@visitors.opaque])

and statement_kind =
  | Assign of place * rvalue
      (** Assigns an [Rvalue] to a [Place]. e.g. [let y = x;] could become
          [y := move x] which is represented as
          [Assign(y, Rvalue::Use(Operand::Move(x)))]. *)
  | SetDiscriminant of place * variant_id
      (** Not used today because we take MIR built. *)
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
  | Drop of place * fn_ptr * drop_kind * block
      (** Drop the value at the given place.

          Depending on [DropKind], this may be a real call to [drop_glue], or a
          conditional call that should only happen if the place has not been
          moved out of. See the docs of [DropKind] for more details; to get
          precise drops use [--precise-drops].

          Fields:
          - [place]
          - [fn_ptr]: Reference to the [drop_glue] code to call on drop.
          - [kind]
          - [on_unwind] *)
  | Assert of assertion * abort_kind * block
      (** Fields:
          - [assert]
          - [on_failure]
          - [on_unwind] *)
  | InlineAsm of inline_asm * block option * block list * block
      (** An inline assembly block.

          Fields:
          - [asm]
          - [fallthrough]: Next block if the control-flow continues without
            jumping. Absent for [naked_asm!] and [noreturn].
          - [labels]: Targets of [[AsmOperand::Label]] operands.
          - [on_unwind]: Action to be taken if the inline assembly unwinds. *)
  | Call of call * block
      (** Fields:
          - [call]
          - [on_unwind] *)
  | Switch of switch_data * block list
      (** Fields:
          - [data]
          - [branches] *)
  | Loop of block
  | Break of int
      (** Break out of one or more loops. The [usize] gives the index of the
          loop to break from, counting inside-out: * 0: break from the innermost
          loop (the current loop) * 1: break from the second innermost loop *
          ... *)
  | Continue of int
      (** Continue to the start of a loop. The [usize] gives the index of the
          loop to continue to, counting inside-out: * 0: continue to the start
          of the innermost loop (the current loop) * 1: continue to the start of
          the second innermost loop * ... *)
  | Panic of name * block
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
  | Nop  (** No-op. *)
[@@deriving
  show,
  eq,
  ord,
  visitors
    {
      name = "iter_statement_base";
      monomorphic = [ "env" ];
      variety = "iter";
      ancestors = [ "iter_trait_impl" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_statement_base";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_trait_impl" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]

let rec hash_block : block -> int =
 fun (x : block) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine 0 (hash_span x.span))
       (hash_block_id x.block_id))
    ((HashBasic.hash_list hash_statement) x.statements)

and hash_block_id : block_id -> int = fun (x : block_id) -> BlockId.hash_id x

and hash_statement : statement -> int =
 fun (x : statement) ->
  HashBasic.combine
    (HashBasic.combine
       (HashBasic.combine
          (HashBasic.combine 0 (hash_span x.span))
          (hash_statement_id x.statement_id))
       (hash_statement_kind x.kind))
    ((HashBasic.hash_list HashBasic.hash_string) x.comments_before)

and hash_statement_id : statement_id -> int =
 fun (x : statement_id) -> StatementId.hash_id x

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
  | Drop (x0, x1, x2, x3) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine
              (HashBasic.combine 6 (hash_place x0))
              (hash_fn_ptr x1))
           (hash_drop_kind x2))
        (hash_block x3)
  | Assert (x0, x1, x2) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine 7 (hash_assertion x0))
           (hash_abort_kind x1))
        (hash_block x2)
  | InlineAsm (x0, x1, x2, x3) ->
      HashBasic.combine
        (HashBasic.combine
           (HashBasic.combine
              (HashBasic.combine 8 (hash_inline_asm x0))
              ((HashBasic.hash_option hash_block) x1))
           ((HashBasic.hash_list hash_block) x2))
        (hash_block x3)
  | Call (x0, x1) ->
      HashBasic.combine (HashBasic.combine 9 (hash_call x0)) (hash_block x1)
  | Switch (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 10 (hash_switch_data x0))
        ((HashBasic.hash_list hash_block) x1)
  | Loop x0 -> HashBasic.combine 11 (hash_block x0)
  | Break x0 -> HashBasic.combine 12 (HashBasic.hash_int x0)
  | Continue x0 -> HashBasic.combine 13 (HashBasic.hash_int x0)
  | Panic (x0, x1) ->
      HashBasic.combine (HashBasic.combine 14 (hash_name x0)) (hash_block x1)
  | UnwindTerminate -> 15
  | UnwindResume -> 16
  | Return -> 17
  | UndefinedBehavior -> 18
  | Nop -> 19
