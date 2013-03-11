Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import Utils Lattices CLattices.

Require Import TMUInstr.
Require Import Abstract Rules AbstractMachine.

Require Import Concrete ConcreteMachine CodeGen CodeSpecs.
Require Import FaultRoutine.

Require Import Simulation.

Set Implicit Arguments.
Local Open Scope Z_scope. 
Coercion Z_of_nat : nat >-> Z.

Section Refinement.

Context {L: Type}
        {Latt: JoinSemiLattice L}
        {CLatt: ConcreteLattice L}.

(** The fault handler code and its correctness *)
Definition fetch_rule_withsig := (fun opcode => existT _ (labelCount opcode) (fetch_rule opcode)).
Definition faultHandler := @CodeGen.faultHandler L fetch_rule_withsig.

(* Bit more glue *)
Lemma our_handler_correct_succeed : 
  forall m i s raddr c opcode vls  pcl  olr lpc op1l op2l op3l,
  forall (INPUT: cache_hit c (mvector opcode op1l op2l op3l pcl))
         (RULE: apply_rule (fetch_rule opcode) vls pcl = Some (olr,lpc))
         (GLUE: glue vls = (op1l, op2l, op3l)),
    exists c',
    runsToEscape (CState c m faultHandler i (CRet raddr false false::s) (0,handlerLabel) true)
                 (CState c' m faultHandler i s raddr false) /\
    handler_final_mem_matches' olr lpc c c' false.
Proof.
  intros. 
  exploit (@handler_correct_succeed _ _ _ fetch_rule_withsig opcode); eauto.
  unfold glue in *. inv GLUE. auto. 
Qed.  
               
Inductive match_stacks : list (@StkElmt L) ->  list (@CStkElmt L) -> Prop :=
| ms_nil : match_stacks nil nil
| ms_cons_data: forall a s cs, 
                  match_stacks s cs ->
                  match_stacks (AData a :: s) (CData a :: cs)
| ms_cons_ret: forall a r s cs, 
                  match_stacks s cs ->
                  match_stacks (ARet a r:: s) (CRet a r false:: cs).

Inductive match_states : @AS L -> @CS L -> Prop :=
|  ms: forall m i astk tmuc cstk pc
              (STKS: match_stacks astk cstk),
         match_states (AState m i astk pc)
                      (CState tmuc m faultHandler i cstk pc false)
.

(** Aux functions yet to be defined - or specified at least *)
Variable c_to_a_stack : list (@CStkElmt L) -> list (@StkElmt L). 

Axiom match_stacks_obs : forall s s', 
    match_stacks s s' ->
    c_to_a_stack s' = s.
Hint Rewrite match_stacks_obs.

(** Observing a concete cache is just projecting it a the abstract level *)
Definition observe_cstate (cs: @CS L) : @AS L := 
  match cs with 
    | CState c m fh i s pc p => AState m i (c_to_a_stack s) pc
  end.
           
(* DD: Don't be tempted to add success s1 as a hypothesis... *)
Axiom final_step_preserved: 
  forall s1 s2,
    (forall s1', ~ step_rules s1 s1') ->
    (match_states s1 s2) ->
    (forall s2', ~ cstep s2 s2')
    /\ s1 = observe_cstate s2.

Lemma handler_cache_hit_read: forall rl m rpcl tmuc,
                                handler_final_mem_matches' (Some rl) rpcl m tmuc false ->
                                cache_hit_read tmuc false rl rpcl. 
Proof.
  intros; inv H ; auto.
Qed.

Lemma step_preserved: 
  forall s1 s1' s2,
    step_rules s1 s1' ->
    match_states s1 s2 ->
    s1 = observe_cstate s2 /\ (exists s2', cstep s2 s2' /\ match_states s1' s2').
Proof.
  intros s1 s1' s2 Hstep Hmatch. inv Hstep. inv Hmatch. 
  split.
  - Case "match_states".
    simpl; erewrite match_stacks_obs; eauto.
  - Case "cstep". 
    unfold run_tmr in H0.
    destruct (classic (cache_hit tmuc (mvector OpNoop None None None pcl))) as [CHIT | CMISS].
    * exists (CState tmuc m faultHandler i cstk (pcv+1, pcl) false). 
      split.
      eapply cstep_nop with (pcv':= pcv) (pcl':= pcl) (rl0:= rpcl) ; eauto. 
      econstructor  ; eauto. econstructor 3 ; eauto. 
      admit. (* DD: in  MS if cache_hit and apply rule, then the result is in cache-read *)
      inv H0. eapply ms ; eauto.
    * 
(*      exploit (@our_handler_correct_succeed m i cstk (pcv,pcl) tmuc) ; eauto.
      intros [c [Hruns Hmfinal]].
      destruct rl. eapply handler_cache_hit_read in Hmfinal; eauto.
      inv Hruns. clear UPRIV PRIV.
      exists (CState c m faultHandler i cstk (pcv+1, pcl) false). 
      split.
      eapply cstep_nop with  ; eauto. 
      econstructor  ; eauto. econstructor 3 ; eauto. simpl ; eauto.
      econstructor 3 ; eauto. admit. (* if cache_hit then cache-read in MS *)
      inv H2. eapply ms ; eauto.
*)
Admitted.

Axiom succ_preserved: 
  forall s1 s2, 
    match_states s1 s2 -> 
    success s1 <-> c_success s2.

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

Lemma cache_hit_same_content (T: Type): forall opcode op1 op2 op3 pcl c c',
  cache_hit c (mvector opcode op1 op2 op3 pcl) ->
  cache_hit c' (mvector opcode op1 op2 op3 pcl) ->
  forall a, 
    (a = addrOpLabel \/ a = addrTag1 \/ a = addrTag2 \/ a = addrTag3 \/ a = addrTagPC) ->
    index_list_Z a c = index_list_Z a c'.
Proof.
  intros. inv H; inv H0. 
  intuition; match goal with | [HH: a = _ |- _ ] => inv HH end.
  inv OP0. inv OP. congruence.
  destruct op1; inv TAG1 ; inv TAG0; congruence.
  destruct op2; inv TAG2 ; inv TAG4; congruence.
  destruct op3; inv TAG3 ; inv TAG5; congruence.
  inv TAGPC ; inv TAGPC0; congruence.
Qed.  

Lemma index_list_cons (T: Type): forall n a (l:list T),
 index_list n l = index_list (n+1) (a :: l).
Proof.
  intros.
  replace ((n+1)%nat) with (S n) by omega. 
  gdep n. induction n; intros.
  destruct l ; simpl; auto.
  destruct l. auto. 
  simpl. eauto.
Qed. 

Lemma index_list_Z_cons (T: Type): forall i (l1: list T) a, 
  i >= 0 ->
  index_list_Z i l1 = index_list_Z (i+1) (a::l1).
Proof.
  induction i; intros.
  auto.
  simpl. unfold read_m. simpl. 
  replace (Pos.to_nat (p + 1)) with ((Pos.to_nat p)+1)%nat by (zify; omega).
  eapply index_list_cons ; eauto. 
  zify; omega.
Qed. 
  
Lemma index_list_Z_eq (T: Type) : forall (l1 l2: list T), 
  (forall i, index_list_Z i l1 = index_list_Z i l2) ->
  l1 = l2.
Proof.
  induction l1; intros.
  destruct l2 ; auto.
  assert (HCont:= H 0). unfold read_m in HCont. inv HCont. 
  destruct l2.
  assert (HCont:= H 0). unfold read_m in HCont. inv HCont. 
  assert (a = t). 
  assert (Helper:= H 0). unfold read_m in Helper. inv Helper. auto.
  inv H0. 
  erewrite IHl1 ; eauto.
  intros. destruct i.
  erewrite index_list_Z_cons with (a:= t); eauto; try omega.
  erewrite H ; eauto.  
  erewrite index_list_Z_cons with (a:= t); eauto; try (zify ; omega).
  erewrite H ; eauto. symmetry. eapply index_list_Z_cons; eauto. zify; omega.
  destruct l1, l2 ; auto.
Qed.
  
Lemma check_cache_determ: forall opcode op1 op2 op3 pcl cs cs' cs'',
  check_tags opcode op1 op2 op3 pcl cs cs' ->
  check_tags opcode op1 op2 op3 pcl cs cs'' ->
  cs' = cs''.
Proof.
  induction 1 ; intros; inv H; auto; try (solve [ intuition]).
  unfold update_cache_spec_mvec in *.
  assert (H_OTHERS: forall addr,  addr <> addrOpLabel ->  addr <> addrTagPC -> 
                        addr <> addrTag1 -> addr <> addrTag2 -> addr <> addrTag3 ->
                        read_m addr c' = read_m addr c'0) by
      (intros; rewrite <- UPD; auto).
  generalize (cache_hit_same_content L C'HIT C'HIT0). intros Hid.
  cut (c' = c'0). intros Heq ; inv Heq. auto.

  eapply index_list_Z_eq ; eauto.
  intros. 
  destruct (Z_eq_dec i0 addrOpLabel).
    inv e. eauto. destruct (Z_eq_dec i0 addrTag1).
    inv e. eauto. destruct (Z_eq_dec i0 addrTag2).
    inv e. eauto. destruct (Z_eq_dec i0 addrTag3).
    inv e. eapply Hid; eauto. destruct (Z_eq_dec i0 addrTagPC).
    inv e. eapply Hid; eauto. eapply H_OTHERS; eauto.
Qed.

(*
Lemma runsToEnd_pc_increase {T: Type}: forall (step: @CS T -> @CS T -> Prop) n n' cs cs',
  runsToEnd step n n' cs cs'  -> 
  n <= n' .
Proof.
  induction 1; intros.
  omega.
  omega.
Qed.


Lemma runsToEnd_determ {T: Type}: forall (step: @CS T -> @CS T -> Prop)
                                  (step_determ: forall s1 s2 s2', step s1 s2 -> step s1 s2' -> s2 = s2')
                                  n n' cs cs',
   runsToEnd step n n' cs cs' ->
   forall  cs'', runsToEnd step n n' cs cs'' ->
   cs' = cs''.
Proof.
  induction 2; intros.
  
  inv H0. auto.
          eapply @runsToEnd_pc_increase in H5; eauto. zify ; omega.

  inv H3; inv H4.
  zify ; omega.
  
  assert (Heq: cs' = cs''). eapply step_determ; eauto. inv Heq.
  eapply IHrunsToEnd ; eauto.  

  eapply @runsToEnd_pc_increase in H9; eauto. zify ; omega.
  
  assert (Heq: cs' = cs'1). eapply step_determ; eauto. inv Heq.
  eapply IHrunsToEnd ; eauto.  
Qed.
*)
  
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
   
Lemma run_tmu_determ: forall opcode op1 op2 op3 pcl cs cs' cs'',
  run_tmu opcode op1 op2 op3 pcl cs cs' ->
  run_tmu opcode op1 op2 op3 pcl cs cs'' ->
  cs' = cs''.
Proof.
  induction 1; intros; inv H3.
  replace cs'0 with cs' in * by (eapply check_cache_determ ; eauto).
  eapply runsToEscape_determ; eauto.
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
    (allinv'; try reflexivity).
  assert (Heq:= run_tmu_determ H13 H0); eauto. inv Heq.
Admitted.


Require Import LNIwithEvents.

Let aexec_with_trace := sys_trace step_rules success (fun x => x).
Let cexec_with_trace := sys_trace cstep c_success observe_cstate.

Theorem refinement: forall s1 s2 T, 
                      match_states s1 s2 ->
                      cexec_with_trace s2 T ->
                      aexec_with_trace s1 T. 
Proof.
  eapply forward_backward_sim; eauto.
  exact final_step_preserved.
  exact step_preserved.
  exact succ_preserved.
  exact cmach_determ.
Qed.  

End Refinement.


  
