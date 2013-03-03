Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import Monad.
Require Import Lattices.
Require Import TMUObsEquiv.
Require Import TMUInstr.
Require Import TMUAbstract.
Require Import TMURules.
Require Import TMUARules.
Require Import NotionsOfNI.
Require Import LockStepNI.

Set Implicit Arguments.

(** * Non-interference property *)

(** Instantiating the generic lockstep non-interference property for
    our particular abstract machine *)

Section ParamMachine.

Context {T: Type}.
Context {Latt: JoinSemiLattice T}.

Ltac spec_drop_data :=
  (* exploit the spec of drop_data *)
  (exploit drop_data_some; eauto); (intros [?a [?b ?Hin]]);
  match goal with 
    | HH: (drop_data _ (@AState _ ?m ?i ?stk ?pc) = _),
          Hin: In _ _ |- _ =>
      (eapply (drop_data_spec m i pc stk) in Hin;  eauto) ;
        (destruct Hin as [?reta [?rt [?rstk [?dstk [?Hdrop [?Happ ?Hdata]]]]]]); 
        (rewrite HH in * ; allinv);
        move_to_top HH
  end.

Lemma lowstep : forall o as1 as1' as2 as2', 
  low_equiv_full_state o as1 as2 ->
  low_pc o as1  ->
  runSTO step_rules as1 = Some as1' ->
  runSTO step_rules as2 = Some as2' ->
  low_equiv_full_state o as1' as2'.
Proof.
  intros. inv H. 
  repeat red in H0. simpl @apc in H0. simpl @snd in H0. congruence.
 
  runSTO_hint. clear H0.  
  step_in @step_rules. 

  step_in @get_apc. 
  step_in get. 
  
  assert (Hinstr: low_equiv_instr o v v0) by 
    (eapply index_aimem_low_eq_instr  ; eauto). 
 
  fetch_instr.
  inv Hinstr; repeat sto_break_succ idtac. 
  
  Case "Noop".
    inv H0. inv H. 
    step_set_apc; eauto.    

  Case "Add".
    step_pop_astk_data.
    step_pop_astk_data.
    step_set_apc.    
    
    inv LEs; allinv; auto.
    inv H4. inv H2. inv H3.
    constructor 2; auto.
    eapply join_low_equiv_list; eauto.  

  Case "Sub".
    step_pop_astk_data.
    step_pop_astk_data.
    step_set_apc.    
    
    inv LEs; allinv; auto.
    inv H4. inv H2. inv H3.
    constructor 2; auto.
    eapply join_low_equiv_list; eauto.  

  Case "Load".
    step_pop_astk_data.
    
    case_on @index_amem.
    inv LEs; allinv. inv H4. inv LEa.
    SCase "Load from low addresses".
      assert (Hmemv: low_equiv_atom o a2 a0) by
        (eapply index_amem_low_eq_atom with (1 := LEm)  ; eauto).
      fetch_mem.
      step_set_apc.      
      inv Hmemv; (constructor 2 ; eauto).
      constructor; eauto. 
      constructor; eauto with lat.

    SCase "Load from high addresses".
      fetch_mem.
      step_set_apc.
      constructor 2 ; auto with lat.
      
    Case "Store".
    step_pop_astk_data.
    step_pop_astk_data.
    
    unfold apply_rule in H2; simpl in H2.
    unfold apply_rule in H1; simpl in H1.
    fetch_mem.    

    set (assert1 := vl \_/ l <: t0) in *.
    set (assert2 := vl0 \_/ l <: t) in *.
    case_eq assert1 ; case_eq assert2 ; intros;
    (unfold assert1, assert2 in *);
    (rewrite H in *; rewrite H0 in *) ; allinv.
  
    (* step update *)
    step_in @update_amem.
    step_in @get_amem. 
    step_in get.
    (* Didn't manage to get rewriting work *)
    destruct u0, u.    
    exploit (@simpl_match_3 (@AS T)) ; eauto.
    intros [am Ham]; rewrite Ham in Heq2.
    exploit (@simpl_match_3 (@AS T)) ; eauto.
    intros [am' Ham']; rewrite Ham' in Heq1.
    step_set_amem.
    step_set_apc.    
    inv LEs. inv H6.  inv H4.   inv H5. (* invert all these *)
    assert (low_equiv_list (low_equiv_atom o) am am').
    cut (vl \_/ (vl2 \_/ l) = (vl \_/ l \_/ vl2)). intro HH; rewrite HH in *.
    cut (vl0 \_/ (vl1 \_/ l) = (vl0 \_/ l \_/ vl1)). intro HH'; rewrite HH' in *.
    eapply low_equiv_list_update_Z with (8:= Ham) (9:= Ham'); eauto; (symmetry ; eauto).     
    clear assert1 assert2.
    eapply low_equiv_atom_join_value with (v3:=v1) (v5:=v) (v6:= v2); auto.
    (* need to clean this... don't want to do this by hand *)
    rewrite <- join_assoc. 
    replace (vl1 \_/ l) with (l \_/ vl1).
    rewrite join_assoc.  auto.
    rewrite join_comm; auto.
    rewrite <- join_assoc. 
    replace (vl2 \_/ l) with (l \_/ vl2).
    rewrite join_assoc.  auto.
    rewrite join_comm; auto.
    constructor 2; auto.
    symmetry ; auto.

    simpl in *; congruence.
    simpl in *; congruence.
    simpl in *; congruence.
    
  Case "Push".
    step_push_astk.
    destruct a1, a2.
    step_set_apc.
    constructor 2; auto.
  
  Case "Jump".
    step_pop_astk_data.
    step_set_apc.
    inv LEs. inv H2. inv LEa.
    constructor 2 ; auto with lat. 
    constructor; eauto with lat. 
    apply below_lret_low_equiv; auto.

  Case "BranchNZ".
    step_pop_astk_data.
    step_set_apc. 
    inv LEs. inv H2. inv LEa. 
    constructor 2; eauto with lat. 
    constructor; eauto with lat. 
    apply below_lret_low_equiv; auto. 
  
  Case "Call".
     step_pop_astk_data.
     step_pop_args_spec false.          

     case_on @push_args.
     exploit push_args_spec; eauto. clear Heq0.
     intros Heq2. inv Heq2.
     exploit push_args_spec; eauto. clear Heq.
     intros Heq1. inv Heq1.
     
     step_set_apc.
     inv LEs. inv H2. inv LEa.
     SCase "Low Call". 
       simpl. constructor 2; auto. eapply join_minimal; eauto.
       exploit low_equiv_list_app_left ; eauto.
       repeat rewrite rev_length ; eauto. intros Hll0.
       exploit low_equiv_list_app_right ; eauto.
       repeat rewrite rev_length ; eauto. intros Hstk0stk.
       eapply low_equiv_list_app ; eauto.
       
     SCase "High Call".
       simpl. constructor; auto with lat.
       
       exploit low_equiv_list_app_right ; eauto.
       repeat rewrite rev_length ; eauto. intros Hstk0stk.
       rewrite below_lret_adata ; eauto;
         [| intros; rewrite <- in_rev in H; eauto].
       rewrite below_lret_adata ; eauto;
         [| intros; rewrite <- in_rev in H; eauto].
       simpl. rewrite Flowl. constructor; auto.        
       
   Case "Ret".
       step_in @get_astk.
       step_in get.
       spec_drop_data.
       spec_drop_data.
       exploit low_equiv_drop ; eauto. 
       intros [HspecRet HspecDstk].
       
       clear H4 H0. inv HspecRet. inv LEa.
       destruct rt0. 
       SCase "Value return". inv H2. 
       SCase "No return". 
       simpl in *. 
       step_set_apc. 
       constructor 2 ; eauto.

       destruct rt0. 
       SCase "Value return". inv H2. 
       SCase "No return". 
       simpl in *. 
       step_set_apc. 
       constructor ; eauto.
       eapply below_lret_low_equiv; eauto.

       
   Case "VRet".
       step_in @get_astk.
       step_in get.
              
       (* exploit the spec of drop_data *)
       spec_drop_data.
       spec_drop_data.
       exploit low_equiv_drop ; eauto. 
       intros [HspecRet HspecDstk].
       clear H4 H0. 
       inv HspecRet. 
       destruct reta0, reta.      
       destruct rt0.        
       SCase "Value return".

       repeat sto_break_succ idtac.
       inv LEs; (rewrite <- H4 in *; try rewrite <- H5 in *;
                 try rewrite <- H3 in *). 
       simpl in H. allinv.
       simpl in H; simpl in H0. allinv.
       inv H5.
       simpl in *.
       destruct a1, a2. 
       step_push_astk.
       step_set_apc. 
       inv LEa. inv LEa0; (constructor 2; eauto). 
       constructor; auto with lat.
       constructor; eauto. 
       simpl. eapply below_lret_low_equiv; eauto.
       inv H1.
       SCase "Return Void". inv H1.
  Case "Halt". inv H2.    
Qed.
       
Lemma highstep : forall o as1 as1', 
  ~low_pc o as1 ->
  runSTO step_rules as1 = Some as1' ->
  ~low_pc o as1' ->
  low_equiv_full_state o as1 as1'.
Proof.
  intros.
  destruct as1. destruct apc. 
  assert (t <: o = false). destruct (flows_dec t o); auto. 
  unfold low_pc in * ; simpl in *. congruence.
  clear H. runSTO_hint. 

  step_in @step_rules. 
  step_in @get_apc. 
  step_in get.
  fetch_instr.
  destruct v; repeat (sto_break_succ idtac); allinv.

  Case "Noop".
    simpl in *; allinv.
    step_set_apc.
    constructor; eauto. 

  Case "Add".
    step_pop_astk_data.    
    step_pop_astk_data.    
    step_set_apc.        
    constructor; eauto. 

  Case "Sub".
    step_pop_astk_data.    
    step_pop_astk_data.    
    step_set_apc.        
    constructor; eauto. 

  Case "Push".
    step_push_astk.
    destruct a. step_set_apc.
    constructor; eauto.

  Case "Load".
    step_pop_astk_data.
    fetch_mem. 
    step_set_apc.
    constructor; eauto.

  Case "Store".
    step_pop_astk_data.
    step_pop_astk_data.
    fetch_mem. 

    unfold apply_rule in * ; simpl in *.
    set (assert1 := vl \_/ t <: t0) in *.
    case_eq assert1; intros;
    (unfold assert1 in *);
    (rewrite H in *; simpl in *) ; allinv.
    
    step_in @update_amem.
    step_in @get_amem.
    step_in get.
    destruct u.
    exploit (@simpl_match_3 (@AS T)) ; eauto. intros [am' Ham'].
    rewrite Ham' in *. 
    
    destruct (flows_dec t0 o).
      assert (t <: t0 = true) by eauto with lat.
      assert (t <: o = true) by eauto with lat. congruence.
      assert ((vl \_/ vl0) \_/ t <: o = false). eauto using not_flows_not_join_flows_right.
      assert (low_equiv_list (low_equiv_atom o) am' amem).
      eapply update_list_Z_high with (4:= Heq) (5:= Ham'); eauto with lat.
    step_set_amem.
    step_set_apc.    
    constructor ; eauto. symmetry ; auto.
    
  Case "Jump".
    step_pop_astk_data.
    step_set_apc.
    constructor ; eauto with lat.   

  Case "BranchNZ".
    step_pop_astk_data.
    step_set_apc.
    constructor ; eauto with lat.   
    
  Case "Call".
    step_pop_astk_data.
    step_pop_args_spec false. 
     
     case_on @push_args.
     exploit push_args_spec; eauto. clear Heq.
     intros Heq0. inv Heq0.
     
     step_set_apc.
     constructor; eauto with lat.     
     
     simpl. 
     do 2 
       (erewrite below_lret_adata; eauto; 
         try (intros; eapply in_rev in H ; eauto)).
     simpl. rewrite H2; auto.
       
   Case "Ret".
     step_in @get_astk.
     step_in get.
     spec_drop_data.
     destruct rt.        
     SCase "Value return". destruct reta; inv H0.
     SCase "Return Void". destruct reta as [reta retal]. simpl in *.
        step_set_apc. 
        destruct (flows_dec retal o) ; auto. eelim H1. 
        eelim H1 ; unfold low_pc ; simpl ; auto.
        constructor ; eauto. 
        rewrite below_lret_adata; eauto.
        simpl. rewrite e. auto.
 
   Case "Ret".
     step_in @get_astk.
     step_in get.
     spec_drop_data.
     destruct rt.        
     SCase "Value return". 
        destruct reta as [reta retal].
        repeat sto_break_succ idtac.
        remember (dstk++(ARet (reta,retal) true)::rstk) as l;
          destruct l ; (simpl in H3; allinv). 
        simpl in H. allinv. 
        destruct v; allinv. 
        destruct a0. 
        step_push_astk. allinv.
        step_set_apc. 
        destruct (flows_dec retal o); auto.
        eelim H1 ; unfold low_pc ; simpl ; auto. 
        (constructor; eauto). 
        rewrite Heql. simpl. 
        rewrite below_lret_adata; eauto.  simpl.
        rewrite e; auto.
        
     SCase "Return Void".
        destruct reta. inv H0. 
Qed. 



Lemma highlowstep : forall o as1 as1' as2 as2', 
  low_equiv_full_state o as1 as2 ->
  ~low_pc o as1 ->
  runSTO step_rules as1 = Some as1' ->
  low_pc o as1' ->
  runSTO step_rules as2 = Some as2' ->
  low_pc o as2' ->
  low_equiv_full_state o as1' as2'.
Proof.
  intros.
  generalize H3 H1.  
  runSTO_hint.  
  inv H; [clear H0 | eelim H0 ; unfold low_pc ; simpl ; auto].
  
  step_in @step_rules.
  step_in @get_apc.
  step_in get.
  (* v is Ret or VRet *)
  remember v as instr ; destruct instr;
  try solve [
    runSTO_hint;
    (exploit step_rules_non_ret_label_pc ; eauto) ;
    (try solve 
      [(intro Hcont; inv Hcont; rewrite bot_flows in Flowl1; intuition) | congruence]);
    (intros [l' [pc' [Hcont1 Hcont2]]]);
    (eapply low_not_high in Hcont1 ; eauto);
    (rewrite Hcont1 in Flowl1 ; inv Flowl1)].
  clear Heq0.
  (* v0 is Ret or VRet *)
     remember v0 as instr ; destruct instr;
       try solve [    runSTO_hint;
         (exploit step_rules_non_ret_label_pc ; eauto) ;
         (try solve 
           [(intro Hcont; inv Hcont; rewrite bot_flows in Flowl1; intuition) | congruence]);
         (intros [l' [pc' [Hcont1 Hcont2]]]);
         (eapply low_not_high in Hcont1 ; eauto);
         (rewrite Hcont1 in Flowl2 ; inv Flowl2)].

  Case "P1 is Ret".
  SCase "P2 is Ret". clear Heq Heqinstr Heqinstr0.   
    fetch_instr.
    step_in @get_astk.
    step_in get.
    spec_drop_data.
    spec_drop_data.
    rewrite below_lret_adata in LEsH; eauto. 
    rewrite below_lret_adata in LEsH; eauto. 
    clear H6 H9.
    
    (* both do not return any value *)
    destruct reta, reta0.
    destruct rt, rt0; repeat (sto_break_succ idtac). 
    inv H3. inv H1. inv H3. 
    simpl in *; allinv. 
    step_set_apc. 
    inv H2. inv H4. 
    rewrite H0 in *.  rewrite H1 in *. 
    inv LEsH. inv H4. inv LEa.
    constructor 2 ; eauto. congruence.
       
 SCase "P2 is Vret". (* contradiction *)
   fetch_instr.
   step_in @get_astk.
   step_in get.
   spec_drop_data.
   spec_drop_data.
   rewrite below_lret_adata in LEsH; eauto. 
   rewrite below_lret_adata in LEsH; eauto. 
   clear H6 H9. destruct reta, reta0.

    destruct rt, rt0; repeat (sto_break_succ idtac). 
    inv H1. inv H3. simpl in H0. allinv.
    destruct v ; allinv.
    destruct a0 ; allinv.
    repeat (sto_break_succ idtac). 
    inv H3. destruct a1.
    step_set_apc. 
    inv H2. inv H4.
    inv LEsH ; (rewrite H1 in *; rewrite H2 in *).
    inv H4. inv H0.  inv H4. inv H3. inv H3.

 Case "P1 is VRet". clear Heq0. 
  (* v0 is Ret or VRet *)
     remember v0 as instr ; destruct instr;
       try solve [ runSTO_hint;
         (exploit step_rules_non_ret_label_pc ; eauto) ;
         (try solve 
           [(intro Hcont; inv Hcont; rewrite bot_flows in Flowl1; intuition) | congruence]);
         (intros [l' [pc' [Hcont1 Hcont2]]]);
         (eapply low_not_high in Hcont1 ; eauto);
         (rewrite Hcont1 in Flowl2 ; inv Flowl2)].

  SCase "P2 is Ret". clear Heq Heqinstr Heqinstr0.   
    fetch_instr.
    step_in @get_astk.
    step_in get.
    spec_drop_data.
    spec_drop_data.
    rewrite below_lret_adata in LEsH; eauto. 
    rewrite below_lret_adata in LEsH; eauto. 
    clear H6 H9.
    
    (* P2 is returning something, not P1. *)
    destruct reta, reta0.
    destruct rt, rt0; repeat (sto_break_succ idtac); try inv H1; try inv H3.    
    simpl in H ; allinv.    
    destruct v2 ; allinv. 
    destruct a1 ; allinv. 
    simpl in LEsH.  
    step_set_apc.
    inv H2; inv H4. 
    rewrite H1 in *. rewrite H2 in *.
    inv LEsH. inv H5; auto.
   
  SCase "P2 is Vret".
   fetch_instr.
   step_in @get_astk.
   step_in get.
   spec_drop_data.
   spec_drop_data.
    rewrite below_lret_adata in LEsH; eauto. 
    rewrite below_lret_adata in LEsH; eauto. 
    clear H6 H9.
    destruct reta, reta0.
    (* Both returning a value *)
    destruct rt, rt0; repeat (sto_break_succ idtac); try inv H1; try inv H3.    
    destruct v, v0; allinv.
    destruct a1, a2; allinv.
    step_set_apc. 
    inv H2 ; inv H4. 
    simpl in LEsH.
    rewrite H2 in *; rewrite H3 in *.
    inv LEsH. inv H6.  
    inv LEa.

    remember (dstk ++ ARet (z0,t0) true :: rstk) as ll1.
    destruct ll1; (simpl in *; allinv).
    remember (dstk0 ++ ARet (z0,t0) true :: rstk0) as ll2.
    destruct ll2; (simpl in *; allinv).
    simpl.

    constructor 2; eauto.
    constructor; eauto. 
    constructor; eauto. 
    econstructor 2; eauto with lat.
    congruence.
Qed.    

Lemma low_lockstep_end : forall o s1 s1' s2,
  low_equiv_full_state o s1 s2 ->
  low_pc o s2 ->
  runSTO step_rules s1 = Some s1' ->
  runSTO step_rules s2 = None ->
  success s2 ->
  False.
Proof.
  intros. 
  apply low_equiv_low_success in H; trivial.
  eapply success_runSTO_None in H; eauto.
  congruence.
Qed.

Theorem lockstep_ni_amach_holds : 
  lockstep_ni_smach step_rules low_equiv_full_state low_pc success.
Proof.
  eapply lockstep_ni_smach_holds ; eauto.
  
  intros. constructor. 
  intros x; auto. 
  intros x y z Hxy Hxz. etransitivity; eauto.
  intros x y ; symmetry; eauto.  
  
  intros. unfold low_pc. 
  destruct (flows_dec (snd (apc s)) o); auto.
  right; congruence.
  
  induction 1;  unfold low_pc ; simpl; intuition. congruence. congruence.

  intros.  destruct s; destruct apc; 
  (unfold success; simpl);
  (destruct (index_list_Z z aimem); intuition);
  (destruct i ; intuition).
  
  eapply lowstep; eauto.
  eapply highstep; eauto.
  eapply highlowstep; eauto.
  eapply low_lockstep_end; eauto.
Qed.

End ParamMachine.