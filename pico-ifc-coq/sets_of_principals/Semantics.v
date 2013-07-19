Require Import Utils.

Set Implicit Arguments.

Record semantics :=
{   state : Type 
  ; event : Type 
  ; step : state -> event+τ -> state -> Prop
  ; init_data : Type
  ; init_state : init_data -> state
}.
