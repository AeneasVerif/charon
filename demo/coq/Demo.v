(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [demo] *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Local Open Scope Primitives_scope.
Module Demo.

(** [demo::choose] *)
Definition choose_fwd (T : Type) (b : bool) (x : T) (y : T) : result T :=
  if b then Return x else Return y
.

(** [demo::choose] *)
Definition choose_back
  (T : Type) (b : bool) (x : T) (y : T) (ret : T) : result (T * T) :=
  if b then Return (ret, y) else Return (x, ret)
.

End Demo .
