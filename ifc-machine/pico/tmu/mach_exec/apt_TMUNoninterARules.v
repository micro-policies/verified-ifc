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
    | HH: (drop_data _ (@Build_AS _ ?m ?i ?stk ?pc) = _),
          Hin: In _ _ |- _ =>
      (eapply (drop_data_spec m i pc stk) in Hin;  eauto) ;
        (destruct Hin as [?reta [?rt [?rstk [?dstk [?Hdrop [?Happ ?Hdata]]]]]]); 
        (rewrite HH in * ; allinv);
        move_to_top HH
  end.


(* This is a completely generic tactic (for STO), independent of proof datails. *)
Ltac monadInv0 rec H :=
  match type of H with
  | (Some _ = Some _) =>
      inversion H; clear H; try subst
  | (None = Some _) =>
      discriminate
  | (Bind ?T ?F ?G ?S = Some (?X,?Y)) => 
      let x := fresh "x" in (
      let s := fresh "s" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (@sto_bind_succ_elim _ _ T F G S X Y H) as [s [x [EQ1 EQ2]]];
      clear H;
      rec EQ1;
      rec EQ2))))
  | (?F _ _ _ _ _ _ _ _ = Some _) => 
      ((progress simpl in H) || unfold F in H); rec H
  | (?F _ _ _ _ _ _ _ = Some _) => 
      ((progress simpl in H) || unfold F in H); rec H
  | (?F _ _ _ _ _ _ = Some _) => 
      ((progress simpl in H) || unfold F in H); rec H
  | (?F _ _ _ _ _ = Some _) => 
      ((progress simpl in H) || unfold F in H); rec H
  | (?F _ _ _ _ = Some _) => 
      ((progress simpl in H) || unfold F in H); rec H
  | (?F _ _ _ = Some _) => 
      ((progress simpl in H) || unfold F in H); rec H
  | (?F _ _ = Some _) => 
      ((progress simpl in H) || unfold F in H); rec H
  | (match ?P with _ => _ end) ?S = Some _ =>
      (let R := fresh "R" in remember P as R; destruct R; rec H) 
  | Some _ = (match ?P with _ => _ end) ?S =>
      (let R := fresh "R" in remember P as R; destruct R; rec H) 
  | (?F _ = Some _) => 
      ((progress simpl in H) || unfold F in H); rec H
  | _ => idtac
  end.

Ltac monadInv H := monadInv0 monadInv H. 

(* The generic tactic does not handle fix's very well.  
To improve things, we can use a specialization of the generic tactic
targeted at this family of proofs. *)
Ltac myMonadInv H :=
match (type of H) with
  | (pop_args ?N ?S = Some (?X,?Y)) => 
    let L := fresh "L" in
    let A := fresh "A" in
    let STK := fresh "stk" in
    let EQ1 := fresh "EQ" in
    let EQ2 := fresh "EQ" in
    (destruct (@pop_args_spec _ _ _ _ _ _ _ _ H) as [L [A [STK [EQ1 EQ2]]]]; 
     clear H; 
     try subst)
  | (push_args ?A ?S = Some (?X,?Y)) => 
     (pose proof (@push_args_spec _ _ _ _ _ _ _ _ H);
      clear H;
      try subst)
  | (drop_data ?N (@Build_AS _ ?M ?I ?S ?PC) = Some(?X,?Y)) =>
     let P := fresh "P" in 
     let D := fresh "D" in 
     (destruct (drop_data_some _ _ _ _ H) as [?a [?b P]]; 
      destruct (drop_data_spec M I PC S _ _ P) as [?reta [?rt [?rstk [?dstk [D [?Happ ?Hdata]]]]]];
      rewrite H in D; allinv) 
  | _ => monadInv0 myMonadInv H
end.


(* Sometimes it is useful to have a "single-step" version that doesn't recurse... *)
Ltac ignore H:= idtac.
Ltac monadInv1 H := monadInv0 ignore H. 

Lemma lowstep : forall o as1 as1' as2 as2', 
  low_equiv_full_state o as1 as2 ->
  low_pc o as1  ->
  runSTO step_rules as1 = Some as1' ->
  runSTO step_rules as2 = Some as2' ->
  low_equiv_full_state o as1' as2'.
Proof.
  intros. inv H. 
  (* repeat red in H0. simpl in H0. simpl @apc in H0. simpl @snd in H0. congruence. *)
  unfold low_pc in H0; simpl in H0; congruence.

  runSTO_hint.
  unfold step_rules in *.

  monadInv1 H1. myMonadInv EQ. monadInv1 EQ0. myMonadInv EQ. 
  monadInv1 H2. myMonadInv EQ. monadInv1 EQ0. myMonadInv EQ. 

  assert (Hinstr: low_equiv_instr o x x1).  
     eapply index_list_Z_low_eq_instr; eauto. 

  inv Hinstr;  myMonadInv EQ1; myMonadInv EQ2. (* this is a bit slow *)
  Case "Noop".
    unfold upd_apc; simpl. 
    eauto. 

  Case "Add".
    inv LEs; allinv; auto. 
    inv H5. inv H4. inv H3. 
    constructor 2; auto. 
    eapply join_low_equiv_list; eauto.  

  Case "Sub".
    inv LEs; allinv; auto.
    inv H5. inv H4. inv H3.
    constructor 2; auto.
    eapply join_low_equiv_list; eauto.  

  Case "Load".
    inv LEs; allinv. inv H3. inv LEa.
    SCase "Load from low addresses".
      assert (Hmemv: low_equiv_atom o (z0,t0) (z2,t2)). 
        eapply index_list_Z_low_eq; eauto.  
      inv Hmemv; (constructor 2 ; eauto).
      constructor; eauto. 
      constructor; eauto with lat.

    SCase "Load from high addresses".
      constructor 2 ; eauto with lat.
      constructor; eauto with lat.    (*APT: don't know why this changed *)

  Case "Store".
    unfold apply_rule in HeqR3; simpl in HeqR3.
    unfold apply_rule in HeqR6; simpl in HeqR6.

    set (assert1 := t \_/ l <: t1) in *.
    set (assert2 := t4 \_/ l <: t6) in *.
    case_eq assert1 ; case_eq assert2 ; intros;
    (unfold assert1, assert2 in *);
    (rewrite H in *; rewrite H1 in *) ; allinv; try congruence.
    clear assert1 assert2.
  
    unfold upd_apc, upd_amem, upd_astk; simpl. 
    inv LEs. inv H7.  inv H5.  inv H6. 
    constructor 2; auto. 

    (* some renaming to allow use of old proof *)
    rename t4 into vl. rename t5 into vl2. rename t into vl0.  rename t0 into vl1.
    cut (vl \_/ (vl2 \_/ l) = (vl \_/ l \_/ vl2)). intro HH; rewrite HH in *.
    cut (vl0 \_/ (vl1 \_/ l) = (vl0 \_/ l \_/ vl1)). intro HH'; rewrite HH' in *. 
    assert (low_equiv_atom o (z, vl0 \_/ l) (z2, vl \_/ l)). 
      eapply low_equiv_atom_join_value with (v2:= 0%Z); eauto. 
    eapply low_equiv_list_update_Z.  (* should clean up *)
    2: apply LEm. 
    7: symmetry; eapply HeqR2. 
    7: symmetry; eapply HeqR5. 
    2: symmetry; eapply HeqR1. 
    2: symmetry; eapply HeqR4. 
    3: auto. 2:auto.
    auto. 
    auto.
    (* need to clean this... don't want to do this by hand *)
    rewrite <- join_assoc. 
    replace (vl1 \_/ l) with (l \_/ vl1).
    rewrite join_assoc.  auto.
    rewrite join_comm; auto.
    rewrite <- join_assoc. 
    replace (vl2 \_/ l) with (l \_/ vl2).
    rewrite join_assoc.  auto.
    rewrite join_comm; auto.

  Case "Push".
    unfold upd_apc, upd_astk; simpl. 
    constructor 2; auto.
  
  Case "Jump".
    unfold upd_apc, upd_astk; simpl. 
    inv LEs. inv H3. inv LEa.
    constructor 2 ; auto with lat. 
    constructor; eauto with lat. 
    apply below_lret_low_equiv; auto.

  Case "BranchNZ".
    unfold upd_apc; simpl. 
    inv LEs. inv H3. inv LEa. 
    constructor 2; eauto with lat. 
    constructor; eauto with lat. 
    apply below_lret_low_equiv; auto. 
  
  Case "Call".
    unfold upd_apc; simpl. 
    inv LEs. inv H3. inv LEa.
    SCase "Low Call". 
       constructor 2; auto. eapply join_minimal; eauto.
       exploit low_equiv_list_app_left ; eauto.
       repeat rewrite rev_length ; eauto. intros Hll0.
       exploit low_equiv_list_app_right ; eauto.
       repeat rewrite rev_length ; eauto. intros Hstk0stk.
       eapply low_equiv_list_app ; eauto.
       
    SCase "High Call".
       constructor; auto with lat.
       
       exploit low_equiv_list_app_right ; eauto.
       repeat rewrite rev_length ; eauto. intros Hstk0stk.
       rewrite below_lret_adata ; eauto;
         [| intros; rewrite <- in_rev in H; eauto].
       rewrite below_lret_adata ; eauto;
         [| intros; rewrite <- in_rev in H; eauto].
       simpl. rewrite Flowl. constructor; auto.        
       
   Case "Ret".
       exploit low_equiv_drop ; eauto. 
       intros [HspecRet HspecDstk].
       
       unfold upd_apc; simpl. 
       inv HspecRet. inv LEa.
       constructor 2; eauto. 
       constructor; eauto.
       eapply below_lret_low_equiv; eauto.

       
   Case "VRet".
       exploit low_equiv_drop ; eauto. 
       intros [HspecRet HspecDstk].

       unfold upd_apc in *; simpl in *. 
       inv HspecRet. 
       inv LEs. inv H3. inv LEa. inv LEa0;  
       constructor 2; eauto. 
       constructor; auto with lat. 
       constructor; eauto. 
       eapply below_lret_low_equiv; eauto. 
       constructor; eauto. 
       constructor; eauto. 
       eapply low_equiv_atom_join_value with (v2 := 0%Z); eauto.
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

  unfold step_rules in H0. 

  myMonadInv H0. 

  Case "Noop".
    simpl in *; allinv.
    constructor; eauto. 

  Case "Add".
    unfold upd_apc, upd_astk in *; simpl in *.
    constructor; eauto. 

  Case "Sub".
    unfold upd_apc, upd_astk in *; simpl in *. 
    constructor; eauto. 

  Case "Push".
    unfold upd_apc, upd_astk in *; simpl in *. 
    constructor; eauto.

  Case "Load".
    unfold upd_apc, upd_astk in *; simpl in *. 
    constructor; eauto.

  Case "Store".

    unfold apply_rule in * ; simpl in *.
    rename t0 into vl.  rename t2 into t0.  (* use old names to avoid having to think below *)
    set (assert1 := vl \_/ t <: t0) in *.
    case_eq assert1; intros;
    (unfold assert1 in *);
    (rewrite H in *; simpl in *) ; allinv.
    
    unfold upd_apc,upd_amem,upd_astk in *; simpl in *. 
    destruct (flows_dec t0 o).
      assert (t <: t0 = true) by eauto with lat.
      assert (t <: o = true) by eauto with lat. congruence.
      assert ((vl \_/ t1) \_/ t <: o = false). eauto using not_flows_not_join_flows_right.
    constructor; auto. 
    symmetry. 
    eapply update_list_Z_high. reflexivity. 4: symmetry; eapply HeqR1. 3:eauto. eauto.
      eauto with lat. 

  Case "Jump".
    unfold upd_apc, upd_astk in *; simpl in *. 
    constructor ; eauto with lat.   

  Case "BranchNZ".
    unfold upd_apc, upd_astk in *; simpl in *. 
    constructor ; eauto with lat.   
    
  Case "Call".
     unfold upd_apc in *; simpl in *. 
     constructor; eauto with lat. 
     simpl. 

     do 2 
       (erewrite below_lret_adata; eauto; 
         try (intros; eapply in_rev in H ; eauto)).
     simpl. rewrite H2; auto.
       
   Case "Ret".
     unfold upd_apc in *; simpl in *. 
     destruct (flows_dec t0 o); auto. 
       eelim H1; unfold low_pc; simpl; auto. 
     constructor; eauto. 
     rewrite below_lret_adata; eauto. 
     simpl. rewrite e; auto. 

   Case "VRet".
     unfold upd_apc, upd_astk in *; simpl in *.
     remember (dstk++(ARet (z0,t0) true)::x1) as l;
       destruct l; try congruence. 
      rewrite <- HeqR2 in Heql. 
      destruct (flows_dec t0 o); auto. 
        eelim H1. unfold low_pc; simpl; auto. 
      constructor; eauto. 
      rewrite Heql. 
      rewrite below_lret_adata; eauto. 
      simpl. rewrite e; auto. 
Qed. 


(* APT: This is as far as I went... *)


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