Require Import Relations.
Require Import EqNat.
Require Import List.
Require Import Utils.

Require Import LNIwithEvents.

Set Implicit Arguments.

(** The abstract specification of a machine *)

Section Vertical.

(** Observers *)
Parameter O: Type. 

(** Events *)
Parameter E: Type.
Parameter e_low: O -> E -> Prop.
Parameter e_succ: E -> Prop.
Parameter e_equiv: O -> relation E.

(** First machine *)
Parameter S1: Type.
Parameter step1: S1 -> S1 -> Prop.
Parameter s_low1: O -> S1 -> Prop.
Parameter s_succ1: S1 -> Prop.
Parameter e1: S1 -> E.
Parameter s_equiv1: O -> relation S1.

(** Second machine *)
Parameter S2: Type.
Parameter step2: S2 -> S2 -> Prop.
Parameter s_low2: O -> S2 -> Prop.
Parameter s_succ2: S2 -> Prop.
Parameter e2: S2 -> E.
Parameter s_equiv2: O -> relation S2.

(** The matching relation between states *)
Variable match_states: S1 -> S2 -> Prop.

(** Constraints on matching states and low-equivalence relation *)
(* These seem reasonable, at least for the translation we want to
prove as a first step.  Because the relation match states is very
strong it's just the equality over the program memory... (not the tmr
part) for proving the simulation, we'll need some additional
invariants. *)

Hypothesis equiv2_match_equiv1 : forall o s2 s2' s1 s1',
  s_equiv2 o s2 s2' ->
  match_states s1 s2 ->
  match_states s1' s2' ->
  s_equiv1 o s1 s1'.

Definition sys_trace1 := sys_trace step1 s_succ1 e1.
Definition sys_trace2 := sys_trace step2 s_succ2 e2.

Definition backward_sim: Prop := 
  forall s1 s2 T,
    match_states s1 s2 ->
    sys_trace2 s2 T ->    
    sys_trace1 s1 T.

Hypothesis match_states_initial: forall s2, exists s1, match_states s1 s2.
     
Lemma sim_lockstep_ni: backward_sim ->
  lockstep_ni step1 e_low s_succ1 e_succ e1 e_equiv s_equiv1 ->
  lockstep_ni step2 e_low s_succ2 e_succ e2 e_equiv s_equiv2.
Proof.
  intros SIM Hlni1. unfold lockstep_ni. 
  intros o s2 s2' T2 T2' Hequiv HT2 HT2'. 

  destruct (match_states_initial s2) as [s1 Hs1s2].
  destruct (match_states_initial s2') as [s1' Hs1s2']. 
  
  assert (sys_trace step1 s_succ1 e1 s1 T2) by (eapply SIM; eauto). 
  assert (sys_trace step1 s_succ1 e1 s1' T2') by (eapply SIM; eauto). 
  
  exploit (Hlni1 o s1 s1'); eauto.
Qed.  

End Vertical.

(* OLD CODE: THIS BRAIN-WRECKING WAS JUST BECAUSE OF THE PLUS SIMULATION
   KEEP IT FOR THE RECORD

(* We'll probably have to constraint a bit more the
   way matching states relate to the low equiv. 
   in particular, even inside the TMM routine, 
   we would like the concrete traces to be in lock step,
   and hence would like to rule out the situation where
   from two low concrete matching states, 
   
   s1 --- TMM ----> s1'
   S
   s2 -> s2'

   From the current definition of the simulation, this is not
   (yet) a contradiction.
 *)
*)