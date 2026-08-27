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
  block_id : block_id;
      (** Integer uniquely identifying this block. To simplify things we
          generate globally-fresh ids when creating a new [Block]. *)
  statements : statement list;
}

and block_id = (BlockId.id[@visitors.opaque])

(** A statement, which can contain nested statements inside loops or switchers.
*)
and statement = {
  span : span;
  statement_id : statement_id;
      (** Integer uniquely identifying this statement among the statmeents in
          the current body. To simplify things we generate globally-fresh ids
          when creating a new [Statement]. *)
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
  | InlineAsm of string * block list * block
      (** An inline assembly block. For now we only preserve the template
          string.

          Fields:
          - [asm]
          - [targets]
          - [on_unwind] *)
  | Call of call * block
      (** Fields:
          - [call]
          - [on_unwind] *)
  | Abort of abort_kind
      (** Panic also handles "unreachable". We keep the name of the panicking
          function that was called. *)
  | Return
  | UnwindResume  (** Unwind out of the current function into its caller. *)
  | Break of int
      (** Break to outer loops. The [usize] gives the index of the outer loop to
          break to: * 0: break to first outer loop (the current loop) * 1: break
          to second outer loop * ... *)
  | Continue of int
      (** Continue to outer loops. The [usize] gives the index of the outer loop
          to continue to: * 0: continue to first outer loop (the current loop) *
          1: continue to second outer loop * ... *)
  | Nop  (** No-op. *)
  | Switch of switch_data * block list
      (** Fields:
          - [data]
          - [branches] *)
  | Loop of block
  | Error of string
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
