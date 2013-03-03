Require Import Relations.
Require Import EqNat.
Require Import List.
Require Import Utils.

Require Import LNIwithEvents.
Set Implicit Arguments.

Axiom classic : forall (P : Prop), P \/ ~ P.

(** Forward simulation, and step-wise lemmas *)
Section Forward.

(** The two machines with a common set for event *)
Variable E: Type.

(** Fist machine *)
Variable S1: Type.
Variable step1: S1 -> S1 -> Prop.
Variable s_succ1: S1 -> Prop.
Variable e1: S1 -> E.

(** Second machine *)
Variable S2: Type.
Variable step2: S2 -> S2 -> Prop.
Variable s_succ2: S2 -> Prop.
Variable e2: S2 -> E.

(** The matching relation between states *)
Variable match_states: S1 -> S2 -> Prop.
 
Hypothesis match_states_final: forall s1 s2,
  (forall s1', ~ step1 s1 s1') ->
  match_states s1 s2 ->
  s_succ1 s1 ->
  (forall s2', ~ step2 s2 s2') /\ (e1 s1) = (e2 s2).

Hypothesis step_preserved: 
  forall s1 s1' s2, 
    step1 s1 s1' ->
    match_states s1 s2 ->
    (e1 s1) = (e2 s2) /\  exists s2', step2 s2 s2' /\ match_states s1' s2'.

Hypothesis succ_match_preserved: forall s1 s2,
  match_states s1 s2 ->
  s_succ1 s1 <->
  s_succ2 s2.

Let sys_trace1 := sys_trace step1 s_succ1 e1.
Let sys_trace2 := sys_trace step2 s_succ2 e2.

Definition forward_sim: Prop := 
  forall s1 s2 T,
    match_states s1 s2 ->
    sys_trace1 s1 T ->    
    sys_trace2 s2 T.

Lemma fwd_sim: forward_sim.
  unfold forward_sim. cofix. intros. 
  inv H0.

  Case "Terminates".
  assert ((forall s2' : S2, ~ step2 s2 s2') /\ e1 s1 = e2 s2).
  apply match_states_final; eauto. destruct H0 as [Hfin2 Hev].
  rewrite Hev.
  eapply @oot_nil ; eauto.
  eelim succ_match_preserved; eauto.

  Case "Steps".
  assert (e1 s1 = e2 s2 /\ (exists s2' : S2, step2 s2 s2' /\ match_states s' s2')).
  eapply step_preserved; eauto. destruct H0 as [Hev [s2' [Hstep2 Hmatch]]].
  rewrite Hev in *. clear Hev.

  assert (e1 s' = e2 s2').
  inv H2. eapply match_states_final; eauto.
  eapply step_preserved ; eauto.
  rewrite H0.
  eapply oot_cons; eauto.
  eapply fwd_sim with s' ; auto.
  rewrite <- H0 ; auto.
Qed.

End Forward.

Section ForwardBackward.

(** The two machines with a common set for event *)
Variable E: Type.

(** Fist machine *)
Variable S1: Type.
Variable step1: S1 -> S1 -> Prop.
Variable s_succ1: S1 -> Prop.
Variable e1: S1 -> E.

(** Second machine *)
Variable S2: Type.
Variable step2: S2 -> S2 -> Prop.
Variable s_succ2: S2 -> Prop.
Variable e2: S2 -> E.

(** The matching relation between states *)
Variable match_states: S1 -> S2 -> Prop.
 
Hypothesis match_states_final: forall s1 s2,
  (forall s1', ~ step1 s1 s1') ->
  match_states s1 s2 ->
  (forall s2', ~ step2 s2 s2') /\ (e1 s1) = (e2 s2).

Hypothesis step_preserved: 
  forall s1 s1' s2, 
    step1 s1 s1' ->
    match_states s1 s2 ->
    (e1 s1) = (e2 s2) /\  exists s2', step2 s2 s2' /\ match_states s1' s2'.

Hypothesis succ_match_preserved: forall s1 s2,
  match_states s1 s2 ->
  s_succ1 s1 <->
  s_succ2 s2.

Let sys_trace1 := sys_trace step1 s_succ1 e1.
Let sys_trace2 := sys_trace step2 s_succ2 e2.

Definition backward_sim: Prop := 
  forall s1 s2 T,
    match_states s1 s2 ->
    sys_trace2 s2 T ->
    sys_trace1 s1 T.

Hypothesis step2_determinism: forall s s' s'', step2 s s' -> step2 s s'' -> s' = s''.

Lemma forward_backward_sim: backward_sim.
Proof.
  unfold backward_sim. cofix.
  intros. inv H0.

  Case "m2 terminates".
    destruct (classic (forall s', ~ step1 s1 s')).
    assert (Hev: e1 s1 = e2 s2) by ((eapply match_states_final; eauto)).
    rewrite <- Hev. 
    apply oot_nil; auto.
    eapply succ_match_preserved ; eauto.
    assert (exists s', step1 s1 s').
    destruct (classic (exists s', step1 s1 s')); eauto.
    eelim H0; eauto.
    destruct H3 as [s' Hs1s'].
    assert (HH: e1 s1 = e2 s2 /\ (exists s2' : S2, step2 s2 s2' /\ match_states s' s2')) by
        (eapply step_preserved ; eauto). destruct HH as  [Hev [s2' [Hcont _]]].
    eelim H1; eauto.
    
  Case "m2 steps". 
    destruct (classic (forall s', ~ step1 s1 s')). 

    SCase "m1 terminates".
    assert (HH : (forall s2' : S2, ~ step2 s2 s2') /\ e1 s1 = e2 s2) by 
      (eapply match_states_final in H0 ; eauto).  
    destruct HH as [Hcont _]. eelim (Hcont s'); eauto.

    SCase "m1 steps or aborts". 
     destruct (classic (exists s', step1 s1 s')); [| eelim H0 ; eauto].

     destruct H3 as [s1' Hs1s'].
     
     SSCase "m1 steps".
     assert (HH: e1 s1 = e2 s2 /\ (exists s2' : S2, step2 s2 s2' /\ match_states s1' s2')) by
         (eapply step_preserved  ; eauto). destruct HH as [Hev [s2' [Hstep Hmatch]]].
     rewrite <- Hev in *. 
     assert (s' = s2') by (eapply step2_determinism ; eauto).
     subst. clear H1.
     assert (HHev': e1 s1' = e2 s2').
         destruct (classic (exists s', step1 s1' s')); eauto.
         destruct H1 as [s1'' Hs1's1'']. 
         eapply step_preserved ; eauto.         
        eapply match_states_final ; eauto. 
       
     rewrite <- HHev'.  
     eapply oot_cons; eauto.
     apply forward_backward_sim with s2' ; auto.
     rewrite HHev'. auto.
Qed.
                              
End ForwardBackward.