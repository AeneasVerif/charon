open Generated_Types
open Generated_Values
open Generated_Expressions
open Generated_Meta
open Generated_GAst
open Identifiers
module BlockId = IdGen ()

(** A "basic block", which contains a linear sequence of statements, followed by
    a terminator, which is where non-linear control-flow happens. *)
type block = { statements : statement list; terminator : terminator }

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
  | TAssert of assertion * block_id * block_id
      (** Assert that the given condition holds, and if not, unwind to the given
          block. This is used for bounds checks, overflow checks, etc.

          Fields:
          - [assert]
          - [target]
          - [on_unwind] *)
  | InlineAsm of string * block_id list * block_id
      (** An inline assembly block. For now we only preserve the template
          string.

          Fields:
          - [asm]
          - [targets]
          - [on_unwind] *)
  | Abort of abort_kind  (** Handles panics and impossible cases. *)
  | Return
  | UnwindResume  (** Unwind out of the current function into its caller. *)
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

(* __REPLACE1__ *)
