(* The concrete machine is deterministic. *)

Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import Utils.

Require Import TMUInstr.
Require Import Abstract Rules AbstractMachine.

Require Import Concrete ConcreteMachine.

Set Implicit Arguments.
Local Open Scope Z_scope. 
(* Coercion Z_of_nat : nat >-> Z. *)

Section Determinism.


Ltac allinv' :=
  allinv ; 
    (match goal with 
       | [ H1:  ?f _ _ = _ , 
           H2:  ?f _ _ = _ |- _ ] => rewrite H1 in H2 ; inv H2
     end).


Lemma cmach_priv_determ: 
  forall s s' s'', 
    cstep_p s s' -> 
    cstep_p s s'' -> 
    s' = s''.
Proof.
  induction 1; intros; 
  match goal with 
      | [HH: cstep_p _ _ |- _ ] => inv HH; try congruence; auto
  end;
  (allinv'; try reflexivity).
  
  Case "Call".
    exploit app_same_length_eq; eauto. intro Heq ; inv Heq.
    exploit app_same_length_eq_rest ; eauto. intro Heq ; inv Heq.
    reflexivity.

  Case "Ret".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.
    
    exploit @c_pop_to_return_spec2; eauto.  move_to_top H11.
    exploit @c_pop_to_return_spec2; eauto. intros. 
    inv H1. inv H2. 
    
    exploit @c_pop_to_return_spec3; eauto. clear H0.
    exploit @c_pop_to_return_spec3; eauto. intros.
    inv H1. 
    reflexivity.
    
  Case "VRet".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto. intros. move_to_top H13.
    exploit @c_pop_to_return_spec2; eauto. intros. 

    exploit @c_pop_to_return_spec3; eauto. intros. 
    generalize H13 ; clear H13 ; intros H13.
    exploit @c_pop_to_return_spec3; eauto. intros.
    inv H1. inv H2.
    reflexivity.
Qed.

(* APT: This doesn't seem to be used.... 
Lemma cache_hit_same_content (T: Type): forall opcode labs pcl c c',
  cache_hit c opcode labs pcl ->
  cache_hit c' opcode labs pcl ->
  forall a, 
    (a = addrOpLabel \/ a = addrTag1 \/ a = addrTag2 \/ a = addrTag3 \/ a = addrTagPC) ->
    index_list_Z a c = index_list_Z a c'.
Proof.
  intros. inv H; inv H0. 
  destruct labs as [[l1 l2] l3]. 
  intuition; match goal with | [HH: a = _ |- _ ] => inv HH end.
  inv OP0. inv OP. congruence.
  inv TAG1 ; inv TAG0; congruence.
  inv TAG2 ; inv TAG4; congruence.
  inv TAG3 ; inv TAG5; congruence.
  inv TAGPC ; inv TAGPC0; congruence.
Qed.  
*)

Lemma check_cache_determ: forall opcode labs pcl cs cs' cs'',
  check_tags opcode labs pcl cs cs' ->
  check_tags opcode labs pcl cs cs'' ->
  cs' = cs''.
Proof.
  induction 1 ; intros; inv H; auto; try (solve [ intuition]).
Qed.
 
Lemma no_unpriv_step : forall s1, priv s1 = false -> forall s2, ~cstep_p s1 s2.
Proof.
  intros. intro S; induction S; simpl in H; try congruence. 
Qed.

Lemma unpriv_star_step : forall s1, priv s1 = false -> forall s2, star cstep_p s1 s2 -> s1 = s2. 
Proof.
  intros.
  inv H0. 
   auto.
   exfalso; eapply no_unpriv_step; eauto.
Qed.

Lemma no_negpc_step : forall s1, fst (pc s1) < 0 -> forall s2, ~cstep_p s1 s2.
Proof.
  intros. intro S; induction S; simpl in H; unfold read_m in *; 
    case_eq (pcv <? 0); intro C; pose proof (Zlt_cases pcv 0) as Q; try rewrite C in *;
      congruence.
Qed.

Lemma negpc_star_step: forall s1, fst (pc s1) < 0 -> forall s2, star cstep_p s1 s2 -> s1 = s2. 
Proof.
  intros.
  inv H0.
    auto.
    exfalso; eapply no_negpc_step; eauto.
Qed.

Lemma runsToEscape_determ: forall cs cs' cs'',
   runsToEscape cs cs' ->
   runsToEscape cs cs'' ->
   cs' = cs''.
Proof.  (* very tedious. there must be some better lemmas lurking. *)
  intros. inv H.
  inv H0. 
     generalize UPRIV0, STAR0, PRIV0.  clear UPRIV0 STAR0 PRIV0. 
     induction STAR; intros. 
       congruence.
       inv STAR0. 
         congruence.
         pose proof (cmach_priv_determ H H0). subst s4.
         case_eq (priv s2); intros. 
           eapply IHSTAR; eauto.
           pose proof (unpriv_star_step H2 STAR). pose proof (unpriv_star_step H2 H1). subst; auto. 
     generalize FAIL, PRIV1, STAR0, PRIV0.  clear FAIL PRIV1 STAR0 PRIV0.
     induction STAR; intros.
       congruence.
       inv STAR0.
         exfalso; eapply no_negpc_step; eauto.
         pose proof (cmach_priv_determ H H0). subst s4.
         case_eq (priv s2); intros.
           eapply IHSTAR; eauto. 
           pose proof (unpriv_star_step H2 STAR). pose proof (unpriv_star_step H2 H1). subst; auto. 
     congruence.              
  inv H0. 
    generalize UPRIV, STAR0, PRIV1, FAIL. clear UPRIV STAR0 PRIV1 FAIL. 
    induction STAR; intros. 
      eapply negpc_star_step; eauto.
      inv STAR0. 
        congruence.
         pose proof (cmach_priv_determ H H0). subst s4.
         case_eq (priv s2); intros. 
           eapply IHSTAR; eauto. 
           pose proof (unpriv_star_step H2 STAR). pose proof (unpriv_star_step H2 H1). subst; auto. 
     generalize FAIL0, PRIV2, STAR0, PRIV1.  clear FAIL0 PRIV2 STAR0 PRIV1.
     induction STAR; intros.
       eapply negpc_star_step; eauto. 
       inv STAR0.
         exfalso; eapply (no_negpc_step FAIL0); eauto.
         pose proof (cmach_priv_determ H H0). subst s4.
         case_eq (priv s2); intros.
           eapply IHSTAR; eauto. 
           pose proof (unpriv_star_step H2 STAR). pose proof (unpriv_star_step H2 H1). subst; auto.  
     congruence.           
  inv H0. 
     congruence.
     congruence.
     auto.
Qed.  
   
Lemma run_tmu_determ: forall opcode l1 l2 l3 pcl cs cs' cs'',
  run_tmu opcode l1 l2 l3 pcl cs cs' ->
  run_tmu opcode l1 l2 l3 pcl cs cs'' ->
  cs' = cs''.
Proof.
  induction 1; intros. inv H2.
  replace cs'0 with cs' in * by (eapply check_cache_determ ; eauto).
  eapply runsToEscape_determ; eauto.

Qed.


Lemma cache_hit_read_determ: forall c rl1 rpcl1 rl2 rpcl2,
  cache_hit_read c rl1 rpcl1 -> 
  cache_hit_read c rl2 rpcl2 ->
  rl1 = rl2 /\ rpcl1 = rpcl2. 
Proof.
  intros. inv H. inv TAG_Res. inv TAG_ResPC. 
  inv H0. inv TAG_Res. inv TAG_ResPC. 
  allinv'. allinv'. intuition.
Qed.


Lemma c_pop_to_return_determ : 
  forall s s1 s2,
    c_pop_to_return s s1 -> 
    c_pop_to_return s s2 -> 
    s1 = s2. 
Proof. 
  induction 1; intros.
  - inv H. reflexivity.
  - inv H0. eauto.
Qed.

Lemma cmach_determ: 
  forall s s' s'', 
    cstep s s' -> 
    cstep s s'' -> 
    s' = s''.
Proof.
  induction 1 ; intros;
  match goal with 
    | [HH: cstep _ _ |- _ ] => inv HH; try congruence; auto
  end;
  repeat (try match goal with
    | [H1: c_pop_to_return ?S ?S1,
       H2: c_pop_to_return ?S ?S2 |- _ ] =>
      let H := fresh in (pose proof (c_pop_to_return_determ H1 H2) as H; eauto; inv H; clear H1 H2)
    | [H1: run_tmu ?OP ?L1 ?L2 ?L3 ?LPC ?S1 ?S2,
       H2: run_tmu ?OP ?L1 ?L2 ?L3 ?LPC ?S1 ?S3 |- _] => 
      let H := fresh in (pose proof (run_tmu_determ H1 H2) as H; eauto; inv H; clear H1 H2)
    | [H1: cache_hit_read ?C ?RL1 ?RPCL1,
       H2: cache_hit_read ?C ?RL2 ?RPCL2 |- _] =>
      let H3 := fresh in let H4 := fresh in 
         (destruct (cache_hit_read_determ H1 H2) as [H3 H4]; eauto; subst; clear H1 H2)
  end;
  try allinv'); 
  try reflexivity.  
  (* One remaining case: Call *)
  Case "call".  
  try rewrite H13 in *.
  pose proof (run_tmu_determ H4 H23) as H; eauto; inv H. 
  destruct (cache_hit_read_determ H5 H24) as [E1 E2]; eauto; subst. 
  assert (args' = args'0). eapply app_same_length_eq; eauto. intuition. subst.
  assert (s' = s'0). eapply app_same_length_eq_rest; eauto. intuition.  subst.
  reflexivity.
Qed.

End Determinism.