Require Import Relations.
Require Import EqNat.
Require Import List.
Require Import Utils.

Require Import NotionsOfNI.

Set Implicit Arguments.

(** The abstract specification of a machine *)
Module Type Machine. 

Parameter Obs: Type. 
Parameter S: Set.
Parameter Low: Obs -> S -> Prop.
Parameter Succ: S -> Prop.
Parameter equiv: Obs -> relation S.
Parameter sys_trace : trace S -> Prop.
Axiom equiv_Low : forall o s s', equiv o s s' -> (Low o s <-> Low o s').
Axiom equiv_equiv: forall o, equivalence _ (equiv o).

End Machine.

Parameter Observer: Type.
Declare Module M1: Machine with Definition Obs:= Observer.
Declare Module M2 : Machine with Definition Obs:= Observer.

(** Now trying to prove that vertical simulation and NI of the abstract machine
   implies non-interference of the concrete machine *)

(** The matching relation between states *)
Variable match_states: M1.S -> M2.S -> Prop.

(** Constraints on matching states and low-equivalence relation *)
(** These seem reasonable, at least for the translation we want to
prove as a first step. *)
(** Because the relation match states is very strong
    it's just the equality over the program memory... (not the tmr part)
    for proving the simulation, we'll need some additional invariants. *)

Hypothesis match_low : forall s1 s2,
  match_states s1 s2 ->
  forall o, M1.Low o s1 <-> M2.Low o s2.

Hypothesis match_succ : forall s1 s2,
  match_states s1 s2 ->
  M1.Succ s1 <-> M2.Succ s2.

(* This looks strong but should hold  *)
Hypothesis equiv_match1 : forall o s2 s2' s1 s1',
  M2.equiv o s2 s2' ->
  match_states s1 s2 ->
  match_states s1' s2' ->
  M1.equiv o s1 s1'.

Hypothesis equiv_match2 : forall o s2 s2' s1 s1',
  M1.equiv o s1 s1' ->
  match_states s1 s2 ->
  match_states s1' s2' ->
  M2.equiv o s2 s2'.

CoInductive lockstep_sim : trace M1.S -> trace M2.S -> Prop :=
| ls_end  : lockstep_sim TNil TNil
| ls_step : forall s1 s2 t1 t2
                   (HstepSIM: lockstep_sim t1 t2)
                   (HstepMATCH: match_states s1 s2),
              lockstep_sim (TCons s1 t1) (TCons s2 t2).

Definition backward_sim: Prop := 
  forall (t2: trace M2.S),
    M2.sys_trace t2 ->    
    exists t1, M1.sys_trace t1 /\ lockstep_sim t1 t2.
(* This definition is not convenient for proving the actual simulation
   (coinduction does not like /\ and exists in conclusions), but it
   matches the other definitions we already have in
   NotionsOfNI.v. Have to find a way of relying on a more traditional
   diagram à la compcert.  *)

Lemma sim_lockstep_ni_helper: forall o t1 t1' t2 t2',
  lockstep_indist M1.equiv M1.Low M1.Succ o t1 t1' ->
  lockstep_sim t1 t2 ->
  lockstep_sim t1' t2' ->
  lockstep_indist M2.equiv M2.Low M2.Succ o t2 t2'.
Proof.
  cofix. intros o T1 T1' T2 T2' Hm1 HsimT1 HsimT2.
  
  inv Hm1.
  Case "M1 stops". 
  inv HsimT1; inv HsimT2. 
  apply li_lockstep_end. 

  Case "M1 low step".
    assert (M1.Low o s2) by ((eapply M1.equiv_Low; eauto); 
                             (eapply equiv_sym; eauto); 
                             (apply M1.equiv_equiv)).      
    inv HsimT1; inv HsimT2.

    apply li_low_lockstep; auto.
    eapply match_low with (s1:= s1) (s2:= s3); eauto.
    eapply equiv_match2 ; eauto. 
    apply (sim_lockstep_ni_helper o t1 t2); eauto.     

  Case "M1 high end".

    inv HsimT1; inv HsimT2.
    inv HstepSIM.
    eapply li_high_end1 ; eauto.
    intros [Hcont1 Hcont2]. 
    eelim H; eauto. split.
    eapply match_low; eauto. 
    eapply match_succ ; eauto.
    eapply equiv_match2 ; eauto.
    
  Case "M2 high end".
  
    inv HsimT1; inv HsimT2.
    inv HstepSIM0.
    eapply li_high_end2 ; eauto.
    intros [Hcont1 Hcont2]. 
    eelim H; eauto. split.
    eapply match_low; eauto. 
    eapply match_succ ; eauto.
    eapply equiv_match2 ; eauto.

  Case "M1 high step".
    inv HsimT1; inv HsimT2.
    inv HstepSIM.
    eapply li_high_high1; eauto.
    intro Hcont.
    eapply match_low with (o:= o) in HstepMATCH; eauto. intuition.
    eapply match_low with (o:= o) in HstepMATCH1; eauto. intuition. 
    eapply equiv_match2 with (1:= H1); eauto.
    eapply equiv_match2 with (1:= H2); eauto.
    eapply sim_lockstep_ni_helper with (1:= H3); eauto.
    constructor; auto.
    constructor; auto.

  Case "M2 high step".
    inv HsimT1; inv HsimT2.
    inv HstepSIM0.
    eapply li_high_high2; eauto.
    intro Hcont.
    eapply match_low with (o:= o) in HstepMATCH0; eauto. intuition.
    eapply match_low with (o:= o) in HstepMATCH1; eauto. intuition. 
    eapply equiv_match2 with (1:= H1); eauto.
    eapply equiv_match2 with (1:= H2); eauto.
    eapply sim_lockstep_ni_helper with (1:= H3); eauto.
    constructor; auto.
    constructor; auto.

  Case "High Low Lockstep".
    inv HsimT1; inv HsimT2.
    inv HstepSIM. inv HstepSIM0.
    eapply li_high_low_lockstep ; eauto.
    intro Hcont.
    eapply match_low with (o:= o) in HstepMATCH; eauto. intuition.
    eapply match_low with (o:= o) in HstepMATCH0; eauto. intuition.
    eapply match_low with (o:= o) in HstepMATCH1; eauto. intuition.
    eapply match_low with (o:= o) in HstepMATCH2; eauto. intuition.
    eapply equiv_match2 with (1:= H3); eauto.
    eapply sim_lockstep_ni_helper with (1:= H4); eauto.
    constructor; auto.
    constructor; auto.
Qed.
     
Lemma sim_lockstep_ni: backward_sim ->
  lockstep_ni M1.sys_trace M1.equiv M1.Low M1.Succ ->
  lockstep_ni M2.sys_trace M2.equiv M2.Low M2.Succ.
Proof.
  intros SIM Hlni1. unfold lockstep_ni. 
  intros o s2 s2' T2 T2' Hequiv HT2 HT2'. 
    
  assert (exists T1, M1.sys_trace T1 /\ lockstep_sim T1 (TCons s2 T2))
    by (eapply SIM; auto). destruct H as [T1 [HT1 Hsim]]. 
  
  assert (exists T1', M1.sys_trace T1' /\ lockstep_sim T1' (TCons s2' T2'))
    by (eapply SIM; auto). destruct H as [T1' [HT1' Hsim']]. 
  
  destruct T1 as [_ | s1]. inv Hsim. 
  destruct T1' as [_ | s1']. inv Hsim'. 

  eapply sim_lockstep_ni_helper; eauto.
  eapply Hlni1; eauto.
  inv Hsim; inv Hsim'; (eapply (@equiv_match1 o s2 s2'); eauto).  
Qed.  


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