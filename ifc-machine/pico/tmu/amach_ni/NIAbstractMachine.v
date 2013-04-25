Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import Lattices.
Require Import AbstractObsEquiv.
Require Import TMUInstr.
Require Import Abstract.
Require Import Rules.
Require Import AbstractMachine.
Require Import LNIwithEvents.

Set Implicit Arguments.

(** * Non-interference property *)

(** Instantiating the generic lockstep non-interference property for
    our particular abstract machine *)

Section ParamMachine.

Context {T: Type}.
Context {Latt: JoinSemiLattice T}.

(* DD: We need to find a way of having dependence easy to deal with...
   Ltac is not exported outside of sections *)
Ltac step_tmr := 
   match goal with
    | [ H: run_tmr _ _ _ = _  |- _ ] => inv H
  end. 

Ltac step_tmr2 :=
  do 2 step_tmr.

Ltac exploit_low :=
    repeat match goal with 
        | [H: low_equiv_list _ (_::_) (_::_) |- _ ] => inv H
        | [H: low_equiv_stkelt _ (AData _) (AData _) |- _ ] => inv H
        | [H: low_equiv_stkelt _ (ARet _ _) (ARet _ _) |- _ ] => inv H
    end.

Ltac spec_pop_return :=
  (exploit @pop_to_return_spec; eauto);
  let stk := fresh "stk" in
  let Hstk := fresh "Hstk" in
  (intros [? [? [? [? [Hstk ?]]]]]);
  match type of Hstk with 
    | ?aastk = _ =>
      match goal with 
        | [HH: pop_to_return aastk _ |- _ ] => (subst ; move_to_top HH)
      end
  end.

Lemma low_equiv_step_pop_to_return: forall o  stk1 stk2 rstk1 rstk2 ,
  low_equiv_list (low_equiv_stkelt o) stk1 stk2 ->
  pop_to_return stk1 rstk1 ->
  pop_to_return stk2 rstk2 ->
  low_equiv_list (low_equiv_stkelt o) rstk1 rstk2.
Proof.
  induction stk1; intros.
  inv H. inv H0.

  inv H.
  inv H1. 
     inv H4. inv H0. eauto.
     inv H0. inv H4. eauto.
Qed.

Lemma lowstep : forall o as1 e as1' as2 e' as2', 
  low_equiv_full_state o as1 as2 ->
  low_pc o as1  ->
  step_rules as1 e as1' ->
  step_rules as2 e' as2' ->
  low_equiv_full_state o as1' as2'.
Proof.
  intros. inv H. inv H0. congruence.
  
  exploit step_rules_instr; eauto. intros [instr1 Hinstr1]. 
  generalize H1 ; clear H1.
  exploit step_rules_instr; eauto. intros [instr2 Hinstr2]. 
  intros H1.
  assert (Hinstr: low_equiv_instr o instr1 instr2) by 
    (eapply index_list_Z_low_eq  ; eauto). 
 
  inv Hinstr; 
    (inv H1 ; try congruence);
    (inv H2 ; try congruence).
  
  Case "Noop".
  step_tmr2. auto.

  Case "Add".
    step_tmr2.
    exploit_low.
    constructor 2; auto.
    eapply join_low_equiv_list; eauto.  

  Case "Sub".
    step_tmr2.
    exploit_low.
    constructor 2; auto.
    eapply join_low_equiv_list; eauto.  

  Case "Load".
    exploit_low. inv LEa.
    
    SCase "Load from low addresses".
    step_tmr2.
    
    assert (Hmemv: low_equiv_atom o  (xv, xl) (xv0, xl0)).
    (eapply index_list_Z_low_eq with (1 := LEm)  ; eauto).
    
    inv Hmemv; (constructor 2 ; eauto).
      constructor; eauto. 
      constructor ; eauto with lat.

    SCase "Load from high addresses".
    step_tmr2.
    constructor 2 ; auto with lat.
      
  Case "Store".
    unfold run_tmr, apply_rule in *; simpl in *. 
    unfold Vector.nth_order in *; simpl in *. 
    set (assert1 := addrl0 \_/ l <: ml0) in *.
    set (assert2 := addrl \_/ l <: ml) in *. 
    case_eq assert1; case_eq assert2 ; intros;
    (unfold assert1 , assert2 in * ) ;
    rewrite H in * ; rewrite H1 in * ; allinv; 
    (try solve [simpl in *; allinv]).
    
    exploit_low. simpl in *. allinv. inv H0.
    assert (low_equiv_list (low_equiv_atom o) m' m'0).
    eapply low_equiv_list_update_Z  with (8:= H11) (9:= H14); eauto with lat.
    eapply low_equiv_atom_join_value with (v0:= xv) ; eauto. 
    constructor 2; auto.
    
  Case "Push".
    step_tmr2. 
    rewrite H9 in Hinstr1; inv Hinstr1.
    rewrite H8 in Hinstr2; inv Hinstr2.
    constructor 2; eauto.

  Case "Jump".
    exploit_low. inv LEa; step_tmr2.    
    constructor 2 ; auto with lat. 
    constructor; eauto with lat. 
    apply below_lret_low_equiv; auto.

  Case "BranchNZ-1".
    exploit_low. inv LEa; step_tmr2.
    constructor 2; eauto with lat. 
    constructor; eauto with lat. 
    apply below_lret_low_equiv; auto. 

  Case "BranchNZ-2".
    exploit_low. inv LEa; step_tmr2. congruence.
    constructor; eauto with lat. 
    apply below_lret_low_equiv; auto. 

  Case "BranchNZ-3".
    exploit_low. inv LEa; step_tmr2. congruence.
    constructor; eauto with lat. 
    apply below_lret_low_equiv; auto. 
    
  Case "BranchNZ-4".
    rewrite H8 in Hinstr2; inv Hinstr2.
    rewrite H9 in Hinstr1; inv Hinstr1.
    exploit_low. inv LEa; step_tmr2.
    constructor 2 ; eauto with lat. 
    constructor; eauto with lat. 
    apply below_lret_low_equiv; auto. 
  
  Case "Call".
     step_tmr2. 
     exploit_low.  inv LEa.
     SCase "Low Call". 
       constructor 2; auto. eapply join_minimal; eauto.
       rewrite H8 in Hinstr2 ; inv Hinstr2.
       rewrite H9 in Hinstr1 ; inv Hinstr1.
       exploit low_equiv_list_app_left ; eauto.
       exploit low_equiv_list_app_right ; eauto. intros.
       eapply low_equiv_list_app ; eauto.
       
     SCase "High Call".
       constructor; auto with lat.
       
       rewrite H8 in Hinstr2 ; inv Hinstr2.
       rewrite H9 in Hinstr1 ; inv Hinstr1.
       exploit low_equiv_list_app_right ; eauto.
       intros Hstk0stk.
       rewrite below_lret_adata ; eauto; [intros; eauto].
       rewrite below_lret_adata ; eauto; [intros; eauto].
       simpl. rewrite Flowl. constructor; eauto.        

  Case "Ret".
       spec_pop_return.
       spec_pop_return.
       exploit low_equiv_step_pop_to_return; eauto.
       intros HspecRet.

       exploit_low.
       step_tmr2.
       simpl in *. 
       inv LEa.
       constructor 2 ; eauto.
       constructor ; eauto.
       eapply below_lret_low_equiv; eauto.
       
   Case "VRet". 
       spec_pop_return.
       spec_pop_return.
       step_tmr2. exploit_low.

       exploit low_equiv_step_pop_to_return; eauto.
       intros HspecRet.  exploit_low. inv H0.
       inv LEa0. inv LEa. 
       constructor 2 ; eauto. 
       constructor 2 ; eauto with lat. 
       constructor; eauto.
       constructor. constructor 2; eauto with lat.
       constructor ; eauto. 
       apply below_lret_low_equiv; eauto.
       inv LEa. constructor ; eauto. 
       constructor; auto. constructor ; eauto with lat.

   Case " Output". 
       step_tmr2. exploit_low.
       inv LEa. 
       constructor 2 ; eauto. 
       constructor 2 ; eauto with lat. 
Qed.

  
Lemma highstep : forall o as1 e as1', 
  ~low_pc o as1 ->
  step_rules as1 e as1' ->
  ~low_pc o as1' ->
  low_equiv_full_state o as1 as1'.
Proof.
  intros.
  destruct as1. destruct apc. 
  assert (t <: o = false). destruct (flows_dec t o); auto. 
  unfold low_pc in * ; simpl in *. congruence.
  clear H. inv H0; step_tmr; eauto with lat. 

  Case "Store".
    unfold run_tmr, apply_rule in * ; simpl in *.
    unfold Vector.nth_order in *; simpl in *. 
    set (assert1 := addrl \_/ t <: ml) in *.
    case_eq assert1; intros;
    (unfold assert1 in *);
    (rewrite H in *; simpl in *) ; allinv.
    
    destruct (flows_dec ml o).
      assert (rpcl <: ml = true) by eauto with lat.
      assert (rpcl <: o = true) by eauto with lat. congruence.
      assert ((addrl \_/ xl) \_/ rpcl <: o = false). eauto using not_flows_not_join_flows_right.
      assert (low_equiv_list (low_equiv_atom o) m' amem).
      eapply update_list_Z_high with (4:= H10) (5:= H11); eauto with lat.
    constructor ; eauto. symmetry ; auto.
        
  Case "Call".
    constructor; eauto with lat.          
    simpl. 
    do 2 
       (erewrite below_lret_adata; eauto; 
        try (intros; eapply in_rev in H ; eauto)).
    simpl. rewrite H2; auto.
       
   Case "Ret".
    unfold Vector.nth_order in *; simpl in *. 
    spec_pop_return.
    exploit @pop_to_return_spec2; eauto. intros. inv H0.
    exploit @pop_to_return_spec3; eauto. intros. inv H0.
    destruct (flows_dec pcl' o) ; auto. eelim H1. 
        eelim H1 ; unfold low_pc ; simpl ; auto.
        
        constructor ; eauto. 
        rewrite below_lret_adata; eauto.
        simpl. rewrite e.
        auto. 

   Case "VRet".
    unfold Vector.nth_order in *; simpl in *. 
    spec_pop_return. 
    exploit @pop_to_return_spec2; eauto. intros. inv H0.
    exploit @pop_to_return_spec3; eauto. intros. inv H0.
    
    destruct (flows_dec pcl' o); auto.
    eelim H1 ; unfold low_pc ; simpl ; auto. 
    (constructor; eauto). simpl.
    rewrite below_lret_adata; eauto.  simpl.
    rewrite e; auto.
Qed. 

Lemma low_lockstep_end : forall o s1 e s1' s2,
  low_equiv_full_state o s1 s2 ->
  low_pc o s2 ->
  step_rules s1 e s1' ->
  success s2 ->
  False.
Proof.
  intros. 
  apply low_equiv_low_success in H; trivial.
  eapply success_runSTO_None in H; eauto.
Qed.

Lemma highlowstep : forall o as1 e as1' as2 e' as2', 
  low_equiv_full_state o as1 as2 ->
  ~low_pc o as1 ->
  step_rules as1 e as1' ->
  low_pc o as1' ->
  step_rules as2 e' as2' ->
  low_pc o as2' ->
  low_equiv_full_state o as1' as2'.
Proof.
  intros.
  inv H ; [clear H0 | eelim H0 ; unfold low_pc ; simpl ; auto].

  exploit step_rules_instr; eauto. intros [instr1 Hinstr1].
  
  (* instr1 is Ret or VRet *)
  destruct instr1;
  try solve [
        (exploit step_rules_non_ret_label_pc ; eauto); try congruence;
        (intros [l' [pc' [Hcont1 Hcont2]]]);
        (eapply low_not_high in Hcont1 ; eauto);
        (rewrite Hcont1 in Flowl1 ; inv Flowl1)].
  
  
  Case "P1 is Ret".
      (inv H1 ; try congruence).
      exploit step_rules_instr; eauto. intros [instr2 Hinstr2].
            
      destruct instr2;
        try solve [
              (exploit step_rules_non_ret_label_pc ; eauto); try congruence;
              (intros [l' [pc' [Hcont1 Hcont2]]]);
              (eapply low_not_high in Hcont1 ; eauto);
              (rewrite Hcont1 in Flowl2 ; inv Flowl2)];
      (inv H3 ; try congruence).

      SCase "P2 is Ret". 
          spec_pop_return. 
          spec_pop_return. 
          exploit @pop_to_return_spec2; eauto. intros H1. inv H1.
          exploit @pop_to_return_spec3; eauto. intros H1. inv H1.
          generalize H11 ; clear H11.
          exploit @pop_to_return_spec2; eauto. intros H1. inv H1.
          exploit @pop_to_return_spec3; eauto. intros H1. inv H1.
          intros. 
          step_tmr2. unfold Vector.nth_order in *; simpl in *. 
          rewrite below_lret_adata in LEsH; eauto.
          rewrite below_lret_adata in LEsH; eauto.
          
          (* both do not return any value *)
          inv H2. inv H4.
          simpl in *. rewrite H2 in *.  rewrite H3 in *.
          exploit_low. inv LEa.
          constructor 2 ; eauto. congruence.
       
      SCase "P2 is Vret". (* contradiction *)
          spec_pop_return.
          spec_pop_return.
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.
          generalize H11 ; clear H11.
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.
          step_tmr2. unfold Vector.nth_order in *; simpl in *. 
          rewrite below_lret_adata in LEsH; eauto. simpl in LEsH.
          inv H2. rewrite H3 in *. 
          rewrite below_lret_adata in LEsH; eauto. simpl in LEsH.
          inv H4. rewrite H2 in *.
          inv LEsH.
          inv H6. 
                      
  Case "P1 is VRet". 
      (inv H1 ; try congruence).
      exploit step_rules_instr; eauto. intros [instr2 Hinstr2].      
      
      destruct instr2;
        try solve [
              (exploit step_rules_non_ret_label_pc ; eauto); try congruence;
              (intros [l' [pc' [Hcont1 Hcont2]]]);
              (eapply low_not_high in Hcont1 ; eauto);
              (rewrite Hcont1 in Flowl2 ; inv Flowl2)];
      (inv H3 ; try congruence).

    
      SCase "P2 is Ret". 
          spec_pop_return.
          spec_pop_return.
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.
          generalize H11 ; clear H11.
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.
          step_tmr2.  unfold Vector.nth_order in *; simpl in *. 
          rewrite below_lret_adata in LEsH; eauto.
          simpl in LEsH.  rewrite below_lret_adata in LEsH; eauto.
          simpl in LEsH.  
          
          inv H2; inv H4.
          rewrite H2 in *. 
          rewrite H3 in *.
          inv LEsH. inv H6.
          
          
     SCase "P2 is Vret".
          spec_pop_return. 
          spec_pop_return.           
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.
          generalize H11 ; clear H11.
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.
          step_tmr2. unfold Vector.nth_order in *; simpl in *. 

          simpl in LEsH. rewrite below_lret_adata in LEsH; eauto.
          rewrite below_lret_adata in LEsH; eauto.
          inv H2 ; inv H4.
          simpl in LEsH.
          rewrite H2 in *; rewrite H3 in *.
          exploit_low. inv LEa.
          
          constructor 2; eauto.
          constructor; eauto.
          constructor; eauto.
          econstructor 2; eauto with lat.
          congruence.
Qed.

(* Theorem lockstep_ni_amach : *)
(*   lockstep_ni_state_evt step_rules low_pc success low_equiv_full_state. *)
(* Proof.  *)
(*   eapply lockstep_ni_state_evt_holds ; eauto. *)

(*   intros; split ; eauto using pc_labels1, pc_labels2.  *)
(*   exact low_pc_dec.  *)
(*   exact success_dec. *)
  
(*   eapply lowstep; eauto. *)
(*   eapply highstep; eauto. *)
(*   eapply highlowstep; eauto. *)
(*   eapply low_lockstep_end; eauto.   *)
(* Qed. *)

End ParamMachine.