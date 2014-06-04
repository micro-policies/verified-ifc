Require Import Utils.
Set Implicit Arguments.

(** The [semantics] record describes the structure of a generic
machine. The [step] relation transitions between elements of type
[state], producing actions which can be either an [event], or the
silent action [τ]. [init_state] specifies how to build the
initial state of an execution from some initial data. *)

Record semantics :=
{   state : Type
  ; event : Type
  ; step : state -> event+τ -> state -> Prop
  ; init_data : Type
  ; init_state : init_data -> state
}.
