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

Definition cache_up2date tmuc :=
  forall opcode vls pcl rl rpcl,
  forall (RULE: apply_rule (fetch_rule opcode) vls pcl = Some (rl, rpcl)),
  forall  op1l op2l op3l, 
  forall (CHIT: cache_hit tmuc (mvector opcode op1l op2l op3l pcl))
         (GLUE: glue vls = (op1l, op2l, op3l)),
    match rl with 
        | Some l => cache_hit_read tmuc false l rpcl
        | None => exists l', cache_hit_read tmuc false l' rpcl
    end.

Inductive match_states : @AS L -> @CS L -> Prop :=
|  ms: forall m i astk tmuc cstk pc
              (CACHE: cache_up2date tmuc)
              (STKS: match_stacks astk cstk),
         match_states (AState m i astk pc)
                      (CState tmuc m faultHandler i cstk pc false).

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
(* DD: Need to be updated later when we add proper behaviors to programs *)
Axiom final_step_preserved: 
  forall s1 s2,
    (forall s1', ~ step_rules s1 s1') ->
    (match_states s1 s2) ->
    (forall s2', ~ cstep s2 s2')
    /\ s1 = observe_cstate s2.

Lemma handler_cache_hit_read_some: 
  forall rl m rpcl tmuc,
    handler_final_mem_matches' (Some rl) rpcl m tmuc false ->
    cache_hit_read tmuc false rl rpcl. 
Proof.
  intros; inv H ; auto.
Qed.

Lemma handler_cache_hit_read_none: 
  forall m rpcl tmuc,
    handler_final_mem_matches' None rpcl m tmuc false ->
    exists rl, cache_hit_read tmuc false rl rpcl. 
Proof.
  intros; inv H ; auto.
Qed.

Ltac allinv' :=
  allinv ; 
    (match goal with 
       | [ H1:  ?f _ _ = _ , 
           H2:  ?f _ _ = _ |- _ ] => rewrite H1 in H2 ; inv H2
     end).

Definition optionlabToZ (ol: option L) : Z := 
      match ol with 
          | None => labToZ bot
          | Some l => labToZ l
      end.

Definition update_cache (tmuc: list (@Atom L)) (opcode: OpCode) (op1 op2 op3: option L) (pcl: L):=
  match upd_m addrOpLabel ((opCodeToZ opcode),handlerLabel) tmuc with 
    | None => tmuc
    | Some tmuc1 => 
      match upd_m addrTag1 ((optionlabToZ op1),handlerLabel) tmuc1  with 
        | None => tmuc
        | Some tmuc2 => 
          match upd_m addrTag2 ((optionlabToZ op2),handlerLabel) tmuc2 with 
              | None => tmuc
              | Some tmuc3 =>
                match upd_m addrTag3 ((optionlabToZ op3),handlerLabel) tmuc3  with 
                  | None => tmuc
                  | Some tmuc4 => 
                    match upd_m addrTagPC ((labToZ pcl),handlerLabel) tmuc4 with
                        | None => tmuc
                        | Some tmuc5 => tmuc5
                    end
                end
          end
      end
  end.

Axiom update_cache_spec : 
  forall tmuc opcode op1 op2 op3 pcl,
    update_cache_spec_mvec tmuc (update_cache tmuc opcode op1 op2 op3 pcl).

Axiom update_cache_hit : 
  forall tmuc opcode op1 op2 op3 pcl,
    cache_hit (update_cache tmuc opcode op1 op2 op3 pcl)
              (mvector opcode op1 op2 op3 pcl).
Hint Resolve update_cache_hit update_cache_spec.

Lemma handler_final_cache_hit_preserved: 
  forall tmuc tmuc' rl opcode op1 op2 op3 rpcl pcl,
    handler_final_mem_matches' rl rpcl tmuc tmuc' false ->
    cache_hit tmuc  (mvector opcode op1 op2 op3 pcl) ->
    cache_hit tmuc' (mvector opcode op1 op2 op3 pcl).
Proof. 
  intros until 0. intros Hfinal HCHIT. inv HCHIT.
  inv Hfinal. unfold update_cache_spec_rvec in *. clear H.
  constructor;
  constructor;
  match goal with 
    | [HTAG: tag_in_mem _ ?addr _
       |- read_m ?addr _ = Some _  ] => 
      (rewrite <- H0 ; eauto); 
      (inv HTAG; eauto);
      (match goal with 
         | [ |- ?a <> ?b ] => try (unfold a, b ; congruence)
       end)
   end.
Qed.

(* Shall we move this directly on the ConcreteLattice class? *)
Axiom labToZ_inj: forall l1 l2, labToZ l1 = labToZ l2 -> l1 = l2.

Lemma opCodeToZ_inj: forall o1 o2, opCodeToZ o1 = opCodeToZ o2 -> o1 = o2.
Proof.
  intros o1 o2 Heq.
  destruct o1, o2; inv Heq; try congruence.
Qed.

Lemma glue_cons_hd: forall n0 a v0 b v3,
  S n0 <= 3 ->
  glue (Vector.cons L a n0 v0) = glue (Vector.cons L b n0 v3) ->
  a = b.
Proof.
  intros.
  inv H0.
  unfold nth_order_option in H3, H4. 
  unfold Vector.nth_order in H2. simpl in H2. auto. 
Qed.

Lemma nth_order_option_cons:
  forall nth n a v,
    nth_order_option (Vector.cons L a n v) (S nth) 
    = nth_order_option v nth.
Proof.
  induction n; intros.
  - unfold nth_order_option. 
    case_eq (le_lt_dec (S nth) 1); case_eq (le_lt_dec nth 0); intros; auto;
    try (zify ; omega).
  - unfold nth_order_option.
    case_eq (le_lt_dec (S (S n)) (S nth)); case_eq (le_lt_dec (S n) nth); intros; auto;
    try (zify ; omega).
    unfold Vector.nth_order. simpl. symmetry.
    erewrite of_nat_lt_proof_irrel ; eauto.
Qed.
    
Lemma glue_cons_tail: 
  forall n0 a v0 b v3,
    (n0 <= 2)%nat ->
    glue (Vector.cons L a n0 v0) = glue (Vector.cons L b n0 v3) ->
    glue v0 = glue v3.
Proof.
  intros. inv H0.
  unfold glue. 
  repeat (rewrite nth_order_option_cons in H3). inv H3. clear H1.
  repeat (rewrite nth_order_option_cons in H4). inv H4. clear H1.
  replace (nth_order_option v0 2) with (nth_order_option v3 2). 
  auto.
  unfold nth_order_option. 
  case_eq (le_lt_dec n0 2); intros; auto.
  zify ; omega.
Qed.
  
Lemma glue_inj: forall n (v1 v2: Vector.t L n), n <= 3 -> glue v1 = glue v2 -> v1 = v2.
Proof.
  intros n v1 v2.
  set (P:= fun n (v1 v2: Vector.t L n) => n <= 3 -> glue v1 = glue v2 -> v1 = v2) in *.
  eapply Vector.rect2 with (P0:= P); eauto.
  unfold P. auto.
  intros.
  unfold P in *. intros. 
  exploit glue_cons_hd; eauto. intros Heq ; inv Heq.
  eapply glue_cons_tail in H1; eauto. 
  exploit H ; eauto. zify; omega.
  intros Heq. inv Heq.
  reflexivity. zify ; omega.
Qed.  

Lemma cache_hit_unique_opcode_pc : 
  forall c opcode opcode' pcl pcl' op1l op1l' op2l op2l' op3l op3l',
  forall
    (CHIT: cache_hit c (mvector opcode op1l op2l op3l pcl))
    (CHIT': cache_hit c (mvector opcode' op1l' op2l' op3l' pcl')),
    pcl = pcl' /\ opcode = opcode'.
Proof.
  intros. inv CHIT; inv CHIT'. split.
  - inv TAGPC; inv TAGPC0. allinv'. 
    eapply labToZ_inj; auto.
  - inv OP; inv OP0. allinv'.
    eapply opCodeToZ_inj ; auto.
Qed.

Lemma cache_hit_unique_ops opcode : 
  forall c  vls vls' op1l op1l' op2l op2l' op3l op3l' rl rl' rpcl rpcl' pcl,
  forall
    (CHIT: cache_hit c (mvector opcode op1l op2l op3l pcl))
    (RULE: apply_rule (fetch_rule opcode) vls pcl = Some (rl, rpcl))
    (GLUE: glue vls = (op1l, op2l, op3l))
    
    (RULE': apply_rule (fetch_rule opcode) vls' pcl = Some (rl', rpcl'))
    (CHIT': cache_hit c (mvector opcode op1l' op2l' op3l' pcl))
    (GLUE': glue vls' = (op1l', op2l', op3l')),

    (op1l = op1l') /\ (op2l = op2l') /\ (op3l = op3l').
Proof.
  intros. 
  destruct op1l, op1l', op2l, op2l', op3l, op3l'; simpl in *;
  (unfold glue, nth_order_option in GLUE, GLUE';
  destruct (le_lt_dec (labelCount opcode) 0); 
    destruct (le_lt_dec (labelCount opcode) 1); 
    destruct (le_lt_dec (labelCount opcode) 2); 
    try congruence);  
  (inv GLUE; inv GLUE'); repeat (split ; auto);
  unfold mvector in CHIT, CHIT'; simpl in *;
  (inv CHIT; inv CHIT';  
  (match goal with 
    | [H1: tag_in_mem c _ (labToZ ?v1), 
       H2: tag_in_mem c _ (labToZ ?v2) |- Some ?v1 = Some ?v2 ] => inv H1; inv H2; allinv'
   end;
   match goal with 
     | [ HH: labToZ _ = labToZ _ |- _] => 
       (eapply labToZ_inj in HH; eauto); 
     inv HH; auto
   end)).
Qed.

Lemma cache_hit_unique opcode : 
  forall c  vls vls' op1l op1l' op2l op2l' op3l op3l' rl rl' rpcl rpcl' pcl,
  forall
    (CHIT: cache_hit c (mvector opcode op1l op2l op3l pcl))
    (RULE: apply_rule (fetch_rule opcode) vls pcl = Some (rl, rpcl))
    (GLUE: glue vls = (op1l, op2l, op3l))
    
    (RULE': apply_rule (fetch_rule opcode) vls' pcl = Some (rl', rpcl'))
    (CHIT': cache_hit c (mvector opcode op1l' op2l' op3l' pcl))
    (GLUE': glue vls' = (op1l', op2l', op3l')),

    vls = vls'.
Proof.
  intros.
  assert (HH:= cache_hit_unique_ops CHIT RULE GLUE RULE' CHIT' GLUE'); eauto.
  decompose [and] HH. inv H. clear HH.
  eapply glue_inj; eauto.
  destruct opcode; simpl; omega. 
  congruence.
Qed.

Hint Constructors cstep run_tmu runsToEscape match_stacks match_states.

Ltac res_label :=
  match goal with 
    | [Hrule: apply_rule _ _ _ = Some (?rl,_) |- _ ] =>
      destruct rl; 
        try (solve [inv Hrule])
  end.

Ltac inv_cache_update :=
  (unfold cache_up2date; intros);
  (exploit handler_final_cache_hit_preserved; eauto);
  intros;              
  match goal with 
    |  [H1 : apply_rule (fetch_rule ?opcode1) ?v1 ?pc1 = _ ,
        H2 : apply_rule (fetch_rule ?opcode2) ?v2 ?pc2 = _ ,
        CHIT: cache_hit _ (mvector _ _ _ _ _) ,
        GLUE: glue _ = _ |- _ ] => 
  (assert (Hopcode: opcode1 = opcode2) by (eapply cache_hit_unique_opcode_pc; eauto); inv Hopcode;
   assert (Hpcl: pc1 = pc2) by (eapply cache_hit_unique_opcode_pc; eauto); inv Hpcl;
   assert (Hvec: v2 = v1) by (eapply cache_hit_unique with (1:= CHIT); eauto); inv Hvec;
   (unfold glue, nth_order_option in GLUE; simpl in GLUE; inv GLUE);
   allinv')
  end;
  try match goal with 
    | [RULE1: apply_rule _ _ _ = _ , 
       RULE2: apply_rule _ _ _ = _  |- _ ] => rewrite RULE1 in RULE2 ; inv RULE2
  end;
  try solve [eapply handler_cache_hit_read_none; eauto
            |eapply handler_cache_hit_read_some; eauto]
.

Lemma step_preserved: 
  forall s1 s1' s2,
    step_rules s1 s1' ->
    match_states s1 s2 ->
    s1 = observe_cstate s2 /\ (exists s2', cstep s2 s2' /\ match_states s1' s2').
Proof.
  intros s1 s1' s2 Hstep Hmatch. inv Hstep. inv Hmatch.
  - Case "Noop".
  {split.
    - SCase "match_states".
      simpl; erewrite match_stacks_obs; eauto.
    - SCase "step".
      unfold run_tmr in H0.
      destruct (classic (cache_hit tmuc (mvector OpNoop None None None pcl))) as [CHIT | CMISS].
      * exists (CState tmuc m faultHandler i cstk (pcv+1, pcl) false).
        res_label. split.
        unfold cache_up2date in CACHE. 
        assert (exists l' : L, cache_hit_read tmuc false l' rpcl).
        eapply CACHE with (1:= H0); eauto. destruct H1 as [ll Hll].
        inv H0. eapply cstep_nop with (rl:= ll) ; eauto. 
        inv H0; eauto.

     * set (tmuc':= (update_cache tmuc OpNoop None None None pcl)) in *.
       assert (CHIT' : cache_hit tmuc' (mvector OpNoop None None None pcl))
         by (eauto using update_cache_hit).
       exploit (@our_handler_correct_succeed m i cstk (pcv,pcl) tmuc'); eauto.
       intros [c [Hruns Hmfinal]].  res_label.
       exists (CState c m faultHandler i cstk (pcv+1, rpcl) false). split.
          + destruct Hmfinal as [[ll Hll] Hspec].
            eapply cstep_nop with _ pcv pcl; eauto.               
          + econstructor ; eauto. 
            inv_cache_update.
  }
 - Case "Add".
  {split.
    - SCase "match_states".
      inv Hmatch. simpl; erewrite match_stacks_obs; eauto.
    - SCase "step".
      unfold run_tmr in H0. inv Hmatch.
      destruct (classic (cache_hit tmuc (mvector OpAdd (Some x1l) (Some x2l) None pcl))) as
          [CHIT | CMISS].
      * inv STKS. inv H4. 
        exists (CState tmuc m faultHandler i ((CData (x1v+x2v,rl))::cs0) (pcv+1, rpcl) false).
        split; eauto.
        unfold cache_up2date in CACHE. 
        eapply cstep_add with x1l x2l pcl i ; eauto.        
        eapply CACHE with (1:= H0); eauto.
        
     * set (tmuc':= (update_cache tmuc OpAdd (Some x1l) (Some x2l) None pcl)) in *.
       assert (CHIT' : cache_hit tmuc' (mvector OpAdd (Some x1l) (Some x2l) None pcl))
         by (eauto using update_cache_hit).
       exploit (@our_handler_correct_succeed m i cstk (pcv,pcl) tmuc'); eauto.
       intros [c [Hruns Hmfinal]]. 
       inv STKS. inv H4.
       exists (CState c m faultHandler i ((CData (x1v+x2v,rl))::cs0) (pcv+1, rpcl) false). split.
          + destruct Hmfinal as [Hll Hspec].
            eapply cstep_add with _ _ pcl _ ; eauto.                
          + econstructor ; eauto. 
            inv_cache_update.
  }
Admitted.

Axiom succ_preserved: 
  forall s1 s2, 
    match_states s1 s2 -> 
    success s1 <-> c_success s2.


(** The concrete machine is deterministic *)
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
  induction 1; intros. inv H2.
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


  
