(** Fault Handler Generation code and correctness proofs. *)

Require Import ZArith.
Require Import List.
Require Import Utils.
Import ListNotations.
Require Vector.

Require Import LibTactics.
Require Import Instr.
Require Import Lattices.
Require Import Concrete.
Require Import ConcreteMachine.
Require Import Rules.
Require Import CLattices.
Require Import CodeTriples. 
Require Import CodeSpecs. 
Require Import CodeGen.
Require Import CLattices.
Require Import ConcreteExecutions.
Require Import Encodable.

Section TMU. 

Open Local Scope Z_scope.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}
        {ELatt : Encodable T}
        {WFCLatt: WfConcreteLattice T Latt CLatt ELatt}.

(* --------------------- TMU Fault Handler code ----------------------------------- *)

(* Compilation of rules *)

Definition genError :=
  push (-1) ++ [Jump].

Definition genVar {n:nat} (l:LAB n) :=
  match l with
  (* NC: We assume the operand labels are stored at these memory
     addresses when the fault handler runs. *)
  | lab1 _ => loadFrom addrTag1
  | lab2 _ => loadFrom addrTag2
  | lab3 _ => loadFrom addrTag3
  | labpc => loadFrom addrTagPC
  end.

Fixpoint genExpr {n:nat} (e: rule_expr n) :=
  match e with
  | L_Bot => genBot
  | L_Var l => genVar l
  (* NC: push the arguments in reverse order. *)
  | L_Join e1 e2 => genExpr e2 ++ genExpr e1 ++ genJoin
 end.

Fixpoint genCond {n:nat} (s: rule_cond n) : code :=
  match s with
  | A_True => genTrue
  | A_LE e1 e2 => genExpr e2 ++ genExpr e1 ++ genFlows
  | A_And s1 s2 => genCond s2 ++ genCond s1 ++ genAnd 
  | A_Or s1 s2 => genCond s2 ++ genCond s1 ++ genOr 
  end.

Definition genApplyRule {n:nat} (am:AllowModify n): code :=
  ite (genCond (allow am))
      (some 
        (genExpr (labResPC am) ++
         genExpr (labRes am))
      )
      none.

Definition genCheckOp (op:OpCode): code :=
  genTestEqual (push (opCodeToZ op)) (loadFrom addrOpLabel).


Section FaultHandler.

Definition fetch_rule_impl_type: Type := forall (opcode:OpCode),  {n:nat & AllowModify n}.
Variable fetch_rule_impl: fetch_rule_impl_type.

Definition genApplyRule' op := genApplyRule (projT2 (fetch_rule_impl op)).

Definition opcodes := 
  [OpNoop; OpAdd; OpSub; OpPush; OpPop; 
   OpLoad; OpStore; OpJump; OpBranchNZ; 
   OpCall; OpRet; OpVRet; OpOutput].

(** Put rule application results on stack. *)
Definition genComputeResults: code :=
  indexed_cases nop genCheckOp genApplyRule' opcodes.

(** Write fault handler results to memory. *)
Definition genStoreResults: code :=
  ifNZ (storeAt addrTagRes ++
        storeAt addrTagResPC ++
        genTrue)
       genFalse.

(** The entire handler *)
Definition faultHandler: code :=
  genComputeResults ++
  genStoreResults ++
  ifNZ [Ret] genError.

End FaultHandler.


(* Connecting vectors of labels to triples of tags. *)
Section Glue.
Import Vector.VectorNotations.
Local Open Scope nat_scope.

Definition nth_labToZ {n:nat} (vls: Vector.t T n) (m:nat) : Z :=
  match le_lt_dec n m with
  | left _ => dontCare
  | right p => labToZ (Vector.nth_order vls p)
  end.

Lemma of_nat_lt_proof_irrel:
  forall (m n: nat) (p q: m < n),
    Fin.of_nat_lt p = Fin.of_nat_lt q.
Proof.
  induction m; intros.
    destruct n.
      false; omega.
      reflexivity.
    destruct n.
      false; omega.
      simpl; erewrite IHm; eauto.
Qed.

Lemma nth_order_proof_irrel:
  forall (m n: nat) (v: Vector.t T n) (p q: m < n),
    Vector.nth_order v p = Vector.nth_order v q.
Proof.
  intros.
  unfold Vector.nth_order.
  erewrite of_nat_lt_proof_irrel; eauto.
Qed.

Lemma nth_order_valid: forall (n:nat) (vls: Vector.t T n) m,
  forall (lt: m < n),
  nth_labToZ vls m = labToZ (Vector.nth_order vls lt).
Proof.
  intros.
  unfold nth_labToZ.
  destruct (le_lt_dec n m).
  false; omega.
  (* NC: Interesting: here we have two different proofs [m < n0] being
  used as arguments to [nth_order], and we need to know that the
  result of [nth_order] is the same in both cases.  I.e., we need
  proof irrelevance! *)
  erewrite nth_order_proof_irrel; eauto.
Qed.

Definition labsToZs {n:nat} (vls :Vector.t T n) : (Z * Z * Z) :=
(nth_labToZ vls 0,
 nth_labToZ vls 1,
 nth_labToZ vls 2).

End Glue.

(* ================================================================ *)
(* Fault-handler Code Specifications                                *)
Section TMUSpecs.

Definition handlerLabel := bot. 

Definition handler_initial_mem_matches 
           (opcode: Z)
           (tag1: Z) (tag2: Z) (tag3: Z) (pctag: Z) 
           (m: memory) : Prop := 
     index_list_Z addrOpLabel m = Some (opcode,handlerTag)
  /\ index_list_Z addrTag1 m = Some (tag1,handlerTag)
  /\ index_list_Z addrTag2 m = Some (tag2,handlerTag)
  /\ index_list_Z addrTag3 m = Some (tag3,handlerTag)
  /\ index_list_Z addrTagPC m = Some (pctag,handlerTag).

Variable fetch_rule_impl: fetch_rule_impl_type.
Variable opcode: OpCode.
Definition n := projT1 (fetch_rule_impl opcode).
Definition am := projT2 (fetch_rule_impl opcode).

Variable vls: Vector.t T n.
Variable pcl: T.
Variable m0: memory.
Hypothesis initial_mem_matches: handler_initial_mem_matches
                                  (opCodeToZ opcode)
                                  (nth_labToZ vls 0)
                                  (nth_labToZ vls 1)
                                  (nth_labToZ vls 2)
                                  (labToZ pcl) m0.

Definition eval_var := mk_eval_var vls pcl.


Ltac clean_up_initial_mem :=
  unfold handler_initial_mem_matches in *;
  intuition;
  jauto_set_hyps; intros.

Lemma genVar_spec_wp: forall v (Q: memory -> stack -> Prop),
      HT (genVar v)
         (fun m s => m = m0 /\ Q m ((labToZ (eval_var v),handlerTag):::s))
         Q.
Proof.
  intros v Q. 
  unfold genVar; subst. inv initial_mem_matches. intuition.
  destruct v; (* split_vc seems to loop *)
    (eapply HT_strengthen_premise;
    try eapply loadFrom_spec_wp; 
    simpl; intros m s [Hmem HQ]; subst;
    try erewrite <- nth_order_valid in HQ; eauto).
Qed.

Lemma genExpr_spec_wp: forall (e: rule_expr n) (Q:memory->stack->Prop),
      HT   (genExpr e)
           (fun m s => m = m0 /\ Q m ((labToZ (eval_expr eval_var e),handlerTag):::s))
           Q.
Proof.
  induction e.  
  - intros.
    eapply HT_strengthen_premise.
    eapply genBot_spec. 
    split_vc. 
 - intros.
   simpl. eapply HT_strengthen_premise.
   eapply genVar_spec_wp. 
   split_vc.  
 - intros. simpl. 
   repeat eapply HT_compose_flip. 
   eapply genJoin_spec. 
   eapply IHe1. 
   eapply HT_strengthen_premise.
   eapply IHe2. 
   split_vc. 
Qed.

Lemma genScond_spec_wp: forall (c: rule_cond n) (Q:memory-> stack ->Prop),
      HT   (genCond c)
           (fun m s =>  m = m0  /\
                        Q m ((boolToZ (eval_cond eval_var c),handlerTag):::s))
           Q.

Proof.
  induction c; intros; simpl. 

  - eapply HT_strengthen_premise.
    eapply genTrue_spec_wp.   
    split_vc. 

  - repeat eapply HT_compose_flip. 
    eapply genFlows_spec. 
    eapply genExpr_spec_wp. 
    eapply HT_strengthen_premise.
    eapply genExpr_spec_wp. 
    split_vc. 
    
  - eapply HT_compose_flip.
    eapply HT_compose_flip. 
    eapply genAnd_spec_wp. 
    eapply IHc1. 
    eapply HT_strengthen_premise.
    eapply IHc2. 
    split_vc. 

  - eapply HT_compose_flip.
    eapply HT_compose_flip. 
    eapply genOr_spec_wp. 
    eapply IHc1. 
    eapply HT_strengthen_premise.
    eapply IHc2. 
    split_vc. 
Qed.

Lemma genApplyRule_spec_Some_wp:
  forall lrpc lr,
    apply_rule am pcl vls = Some (lrpc, lr) ->
    forall Q,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       Q m ((        1, handlerTag)  ::: (* [Some (...)] *)
                            (labToZ lr, handlerTag)  :::
                            (labToZ lrpc, handlerTag)::: s))
           Q.
Proof.
  introv Happly. intros.
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.
  inv Happly; subst.
  
  eapply HT_strengthen_premise. unfold ite.
  eapply HT_compose_bwd.
  eapply ifNZ_spec_existential.
  eapply HT_compose_bwd.
  eapply push_spec_wp.
  
  eapply HT_compose_bwd.
  eapply genExpr_spec_wp.
  eapply genExpr_spec_wp.
  eapply push_spec_wp.
  eapply genScond_spec_wp.
  split_vc.
  unfold eval_var in H2. 
  rewrite H in H2 at 1.
  false; omega.
Qed.


Lemma genApplyRule_spec_None_wp:
    apply_rule am pcl vls = None ->
    forall Q,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       Q m ((0, handlerTag) ::: (* [None] *)
                                         s))
           Q.
Proof.
  introv Happly. intros.
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.
  eapply HT_strengthen_premise. unfold ite.
  eapply HT_compose_bwd.
  eapply ifNZ_spec_existential.
  eapply HT_compose_bwd.
  eapply push_spec_wp.
  
  eapply HT_compose_bwd.
  eapply genExpr_spec_wp.
  eapply genExpr_spec_wp.
  eapply push_spec_wp.
  eapply genScond_spec_wp.
  split_vc. substs.
  split; intros;
  (unfold eval_var in H0; 
  rewrite H in H0 at 1);
  intuition.
Qed.
  
Definition listify_apply_rule (ar: option (T * T)) (s0: stack): stack :=
  match ar with
  | None            => CData (0, handlerTag) :: s0
  | Some (lrpc, lr) => CData (1, handlerTag) ::
                        CData (labToZ lr, handlerTag) ::
                        CData (labToZ lrpc, handlerTag) :: s0
  end.

Lemma genApplyRule_spec_wp:
  forall ar,
    apply_rule am pcl vls = ar ->
    forall Q,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       Q m (listify_apply_rule ar s))
           Q.
Proof.
  intros.
  case_eq ar; intros p ?; subst.
  - destruct p as [lrpc lr].
    eapply genApplyRule_spec_Some_wp; eauto.
  - eapply genApplyRule_spec_None_wp; eauto.
Qed.

Lemma genCond_spec_wp: forall (c: rule_cond n),
  forall b,
    eval_cond eval_var c = b ->
    forall Q,
      HT   (genCond c)
           (fun m s => m = m0 /\ Q m ((boolToZ b, handlerTag) ::: s))
           Q .
Proof.
  induction c; intros; simpl;
    try (simpl in H); subst.

  (* True *)
  eapply HT_strengthen_premise.
  eapply genTrue_spec_wp. split_vc.

  (* Flows *)
  eapply HT_compose_flip.
  eapply HT_compose_flip.
  eapply genFlows_spec. 
  eapply genExpr_spec_wp. 
  eapply HT_strengthen_premise.  
  eapply genExpr_spec_wp. split_vc; eauto.

  (* And *)
  eapply HT_compose_flip.
  eapply HT_compose_flip.
  eapply genAnd_spec_wp.
  eapply IHc1; eauto.
  eapply HT_strengthen_premise. 
  eapply IHc2; eauto. split_vc; eauto.

  (* Or *)
  eapply HT_compose_flip.
  eapply HT_compose_flip.
  eapply genOr_spec_wp.
  eapply IHc1; eauto.
  eapply HT_strengthen_premise. 
  eapply IHc2; eauto. split_vc; eauto.
Qed.

(* XXX: how to best model [option]s and monadic sequencing in the code
   gens?  E.g., for [genApplyRule_spec], I need to handle both [Some
   (Some l1, l2)] and [Some (None, l2)].  Do I do different things to
   memory in these cases? If so I need to distinguish these cases in
   my stack returns.

   Also, modeling [option]s in the generated code might make the
   correctness proof easier? *)

(* NC: Nota bene: we should only need to reason about what
   [genApplyRule] does for the current opcode, since that's the only
   code that is going to run. *)

Lemma genApplyRule_spec_GT:
  forall ar,
    apply_rule am pcl vls = ar ->
      GT (genApplyRule am)
         (fun m s => m = m0)
         (fun m0' s0 m s => m = m0 /\
                            s = listify_apply_rule ar s0).
Proof.
  unfold GT; intros.
  eapply HT_strengthen_premise; eauto.
  - eapply genApplyRule_spec_wp; eauto.
  - simpl; intuition (subst; eauto).
Qed.

Lemma genCheckOp_spec:
  forall opcode', forall s0,
    HT (genCheckOp opcode')
      (fun m s => m = m0 /\
                  s = s0)
      (fun m s => m = m0 /\
                  s = (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode)
                      ,handlerTag) ::: s0).
Proof.
  clean_up_initial_mem.
  intros.
  unfold genCheckOp.
  eapply genTestEqual_spec.
  intros. eapply HT_strengthen_premise.
  eapply push_spec_wp.
  split_vc. subst; eauto. 
  intros. eapply HT_strengthen_premise. eapply loadFrom_spec_wp.
  split_vc. subst; eauto. 
Qed.

Lemma genCheckOp_spec_GT:
  forall opcode',
    GT (genCheckOp opcode')
       (fun m s => m = m0)
       (fun m0' s0 m s => m = m0 /\
                          s = (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode)
                               ,handlerTag) ::: s0).
Proof.
  unfold GT; intros.
  eapply HT_consequence; eauto.
  - eapply genCheckOp_spec; eauto.
  - simpl; intuition (subst; eauto).
  - simpl; intuition (subst; eauto).
Qed.

Section FaultHandlerSpec.

Variable ar: option (T * T).
Hypothesis H_apply_rule: apply_rule am pcl vls = ar.

(* Don't really need to specify [Qnil] since it will never run *)
Definition Qnil: GProp := fun m0' s0 m s => True.
Definition genV: OpCode -> HFun :=
  fun i _ _ => boolToZ (opCodeToZ i =? opCodeToZ opcode).
Definition genC: OpCode -> code := genCheckOp.
Definition genB: OpCode -> code := genApplyRule' fetch_rule_impl.
Definition genQ: OpCode -> GProp :=
         (fun i m0' s0 m s => m = m0 /\
                              s = listify_apply_rule ar s0).

Lemma genCheckOp_spec_GT_push_v:
  forall opcode',
    GT_push_v (genC opcode')
              (fun m s => m = m0)
              (genV opcode').
Proof.
  intros; eapply GT_consequence'.
  eapply genCheckOp_spec_GT.
  eauto.
  intuition (subst; intuition).
Qed.


Lemma opCodeToZ_inj: forall opcode opcode',
  (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode) <> 0) ->
  opcode' = opcode.
Proof.
  intros o o'.
  destruct o; destruct o'; simpl; solve [ auto | intros; false; omega ].
Qed.

Lemma genApplyRule'_spec_GT_guard_v:
  forall opcode',
    GT_guard_v (genB opcode')
               (fun m s => m = m0)
               (genV opcode')
               (genQ opcode').
Proof.
  intros.
  cases (dec_eq_OpCode opcode' opcode) as Eq; clear Eq.
  - eapply GT_consequence'.
    + unfold genB, genApplyRule'.
      subst opcode'.
      fold am.
      eapply genApplyRule_spec_GT; eauto.
    + iauto.
    + (* why does iauto no longer work here?? *)
      subst ar. intros.  subst m1. econstructor. intuition. subst ar. intuition.
  - unfold GT_guard_v, GT, HT.
    intros.
    unfold genV in *.
    pose (opCodeToZ_inj opcode opcode').
    false; intuition. 
Qed. 

Lemma H_indexed_hyps: indexed_hyps _ genC genB genQ genV (fun m s => m = m0) opcodes.
Proof.
  simpl.
  intuition; try (solve
    [ eapply genCheckOp_spec_GT_push_v
    | eapply genApplyRule'_spec_GT_guard_v ]).
Qed.

Lemma genComputeResults_spec_GT:
  GT (genComputeResults fetch_rule_impl)
     (fun m s => m = m0)
     (fun m0' s0 m s => m = m0 /\
                        s = listify_apply_rule ar s0).
Proof.
  intros.
  eapply GT_consequence'.
  unfold genComputeResults.
  eapply indexed_cases_spec with (Qnil:=Qnil).
  - Case "default case that we never reach".
    unfold GT; intros.
    eapply HT_strengthen_premise.    
    eapply nop_spec_wp.
    unfold Qnil; iauto.
  - exact H_indexed_hyps.
  - iauto.
  - Case "untangle post condition".
    simpl.
    assert (0 = 0) by reflexivity.
    assert (1 <> 0) by omega.
    (* NC: Otherwise [cases] fails.  Thankfully, [cases] tells us this
    is the problematic lemma, whereas [destruct] just spits out a huge
    term and says it's ill typed *)
    clear H_apply_rule.
    unfold genV, genQ.
    cases opcode; simpl; intuition.
Qed.

(* Under our assumptions, [genComputeResults] just runs the appropriate
   [genApplyRule]: *)
Lemma genComputeResults_spec:
    forall s0,
      HT   (genComputeResults fetch_rule_impl)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = listify_apply_rule ar s0).
Proof.
  intros.
  eapply HT_consequence'.
  eapply genComputeResults_spec_GT.
  iauto.
  simpl; iauto.
Qed.

Lemma genStoreResults_spec_Some: forall lr lrpc,
  valid_address addrTagRes m0 ->
  valid_address addrTagResPC m0 ->
  ar = Some (lrpc, lr) ->
  forall s0,
    HT genStoreResults
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s =>
        (exists m', upd_m addrTagRes (labToZ lr,handlerTag) m0
                    = Some m'
                 /\ upd_m addrTagResPC (labToZ lrpc,handlerTag) m'
                    = Some m)
        /\ s = (1,handlerTag) ::: s0).
Proof.
  introv HvalidRes HvalidResPC Har_eq; intros.
  unfold listify_apply_rule.
  rewrite Har_eq.
  unfold genStoreResults.

  (* Need to exploit early so that existentials can be unified against
  vars introduced here *)
  eapply valid_store in HvalidRes.
  destruct HvalidRes as [m' ?].
  eapply valid_address_upd in HvalidResPC.
  eapply valid_store in HvalidResPC.
  destruct HvalidResPC as [m'' ?]; eauto.

  eapply HT_strengthen_premise.
  eapply ifNZ_spec_NZ with (v:=1).
  eapply HT_compose_bwd.
  eapply HT_compose_bwd.
  eapply genTrue_spec_wp.
  eapply storeAt_spec_wp.
  eapply storeAt_spec_wp.

  omega.
  simpl; intuition; subst; jauto.
  eauto.
Qed.

Lemma genStoreResults_spec_None:
  ar = None ->
  forall s0,
    HT genStoreResults
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => m = m0 /\
                   s = (0,handlerTag) ::: s0).
Proof.
  introv Har_eq; intros.
  unfold listify_apply_rule.
  rewrite Har_eq.
  unfold genStoreResults.

  eapply HT_strengthen_premise.
  eapply ifNZ_spec_Z with (v:=0).
  eapply genFalse_spec_wp.

  reflexivity.
  jauto.
Qed.

(* The irrelevant memory never changes *)
Lemma genStoreResults_update_cache_spec_rvec:
  valid_address addrTagRes m0 ->
  valid_address addrTagResPC m0 ->
  forall s0,
    HT genStoreResults
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => update_cache_spec_rvec m0 m).
Proof.
  intros.
  unfold update_cache_spec_rvec in *.

  cases ar as Eq_ar.
  destruct p.

  + eapply HT_weaken_conclusion;
    rewrite <- Eq_ar in *.

    eapply genStoreResults_spec_Some; eauto.

    simpl.
    intros;

    jauto_set_hyps; intros.
    eapply transitivity.
    eapply update_list_Z_spec2; eauto.
    eapply update_list_Z_spec2; eauto.

  + eapply HT_weaken_conclusion;
    rewrite <- Eq_ar in *.

    eapply genStoreResults_spec_None; eauto.

    simpl; intuition; subst; auto.
Qed.

Definition handler_final_mem_matches (lrpc: T) (lr: T) (m: memory) (m': memory) :Prop :=
     cache_hit_read m' (labToZ lr) (labToZ lrpc) 
  /\ update_cache_spec_rvec m m'.   (* Nothing else changed *)

Lemma genStoreResults_spec_Some': forall lr lpc,
  valid_address addrTagRes m0 ->
  valid_address addrTagResPC m0 ->
  ar = Some (lpc, lr) ->
  forall s0,
    HT genStoreResults
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => handler_final_mem_matches lpc lr m0 m
                   /\ s = (1,handlerTag) ::: s0).
Proof.
  introv HvalidRes HvalidResPC Har_eq; intros.
  generalize (valid_store _ (labToZ lr,  handlerTag) _ HvalidRes).
  intros [m' Hm'].
  generalize (valid_address_upd _ _ _ _ _ HvalidResPC Hm').
  clear HvalidRes HvalidResPC.
  intros HvalidResPC.
  generalize (valid_store _ (labToZ lpc,  handlerTag) _ HvalidResPC).
  intros [m'' Hm''].
  unfold genStoreResults.
  eapply HT_strengthen_premise.
  eapply ifNZ_spec_NZ with (v := 1); try omega.
  eapply HT_compose_flip.
  eapply HT_compose_flip.
  eapply genTrue_spec_wp.
  simpl.
  eapply storeAt_spec_wp.
  eapply storeAt_spec_wp.
  rewrite Har_eq. simpl.
  intros m s [Hm Hs]. subst.
  eexists.
  generalize (update_list_Z_spec _ _ _ Hm''). intros H1.
  generalize (update_list_Z_spec _ _ _ Hm'). intros H2.
  erewrite update_list_Z_spec2 in H2; eauto; try solve [compute; omega].
  repeat (split; eauto); try econstructor; eauto.
  clear - Hm' Hm''.
  intros addr H1 H2.
  transitivity (read_m addr m'); eapply update_list_Z_spec2; eauto.
Qed.

Lemma genError_specEscape: forall raddr (P: memory -> stack -> Prop),
  HTEscape raddr genError
           P
           (fun m s => (P m s , Failure)).
Proof.
  intros.
  unfold genError.
  eapply HTEscape_compose.
  Focus 2.
  eapply jump_specEscape_Failure.
  eapply HT_strengthen_premise.
  eapply push_spec_wp.
  split_vc. 
Qed.

Definition genFaultHandlerReturn: code := ifNZ [Ret] genError.

Lemma genFaultHandlerReturn_specEscape_Some: forall raddr lr lpc,
  forall s0,
  HTEscape raddr genFaultHandlerReturn
       (fun (m : memory) (s : stack) =>
        handler_final_mem_matches lr lpc m0 m /\
        s = (1, handlerTag) ::: CRet raddr false false :: s0)
       (fun (m : memory) (s : stack) =>
        (s = s0 /\ handler_final_mem_matches lr lpc m0 m, Success)).
Proof.
  intros.
  unfold genFaultHandlerReturn.
  eapply HTEscape_strengthen_premise.
  - eapply ifNZ_specEscape with (v:=1) (Pf:=fun m s => True); intros.
    eapply ret_specEscape.
    auto.
    false.
  - subst.
    intuition.
    jauto_set_goal; eauto.
Qed.

Lemma genFaultHandlerReturn_specEscape_None: forall raddr s0,
 HTEscape raddr genFaultHandlerReturn
   (fun (m : memory) (s : stack) => m = m0 /\ s = (0, handlerTag) ::: s0)
   (fun (m : memory) (s : stack) => (m = m0 /\ s = s0, Failure)).
Proof.
  intros.
  unfold genFaultHandlerReturn.
  eapply HTEscape_strengthen_premise.
  - eapply ifNZ_specEscape with (v := 0) (Pt := fun m s => True); intros. 
    + intuition.
    + eapply genError_specEscape. 
  - intros. 
    subst. 
    intuition.
    jauto_set_goal; eauto.
Qed.
 
Lemma faultHandler_specEscape_Some: forall raddr lr lpc,
  valid_address addrTagRes m0 ->
  valid_address addrTagResPC m0 ->
  ar = Some (lpc, lr) ->
  forall s0,
    HTEscape raddr (faultHandler fetch_rule_impl)
             (fun m s => m = m0 /\
                         s = (CRet raddr false false::s0))
             (fun m s => ( s = s0 /\
                           handler_final_mem_matches lpc lr m0 m
                         , Success )).
Proof.
  intros.
  unfold faultHandler.
  eapply HTEscape_compose.
  - eapply genComputeResults_spec.
  - eapply HTEscape_compose.
    + eapply genStoreResults_spec_Some'; eauto.
    + eapply genFaultHandlerReturn_specEscape_Some; auto.
Qed.

Lemma faultHandler_specEscape_None: forall raddr,
  ar = None -> 
  forall s0,
    HTEscape raddr (faultHandler fetch_rule_impl)
             (fun m s => m = m0 /\ s = s0)
             (fun m s => (m = m0 /\ s = s0
                         , Failure)).
Proof.
  intros.
  unfold faultHandler.
  eapply HTEscape_compose.
  - eapply genComputeResults_spec.
  - eapply HTEscape_compose.
    + eapply genStoreResults_spec_None; eauto.
    + eapply genFaultHandlerReturn_specEscape_None; auto.
Qed.

End FaultHandlerSpec.

End TMUSpecs.

(** Main result of this file : the correctness theorems of the fault handler generator *)
Section HandlerCorrect.

Variable get_rule : forall (opcode:OpCode), {n:nat & AllowModify n}.
Definition handler : list Instr := faultHandler get_rule.

(* Connecting to the definition used in Concrete.v *)
Lemma init_enough: forall {n} (vls:Vector.t T n) m opcode pcl,
    cache_hit m (opCodeToZ opcode) (labsToZs vls) (labToZ pcl) ->
    handler_initial_mem_matches 
      (opCodeToZ opcode) 
      (nth_labToZ vls 0)  
      (nth_labToZ vls 1)
      (nth_labToZ vls 2)
      (labToZ pcl)
      m.
Proof.
  intros. unfold labsToZs in H. 
  inv H. inv UNPACK. inv OP. inv TAG1. inv TAG2. inv TAG3. inv TAGPC. 
  econstructor; jauto.
Qed.

Theorem handler_correct_succeed :
  forall opcode vls pcl c m raddr s i lr lpc,
  forall (INPUT: cache_hit c (opCodeToZ opcode) (labsToZs vls) (labToZ pcl))
         (RULE: apply_rule (projT2 (get_rule opcode)) pcl vls = Some (lpc,lr)),
    exists c',
    runsToEscape (CState c m handler i (CRet raddr false false::s) (0,handlerTag) true)
                 (CState c' m handler i s raddr false) /\
    handler_final_mem_matches lpc lr c c'.
Proof.
  intros.
  assert (valid_address addrTagRes c).
    inv INPUT. inv TAGR. eapply index_list_Z_valid; eauto. 
  assert (valid_address addrTagResPC c).
    inv INPUT. inv TAGRPC. eapply index_list_Z_valid; eauto.
  edestruct (faultHandler_specEscape_Some get_rule opcode vls pcl c) 
      as [stk1 [cache1 [pc1 [priv1 [[P1 P2] [P3 P4]]]]]]; eauto. 
   eapply init_enough; auto. 
  apply code_at_id. 
  exists cache1. 
  inversion P3.  subst. 
  intuition.
  apply P4. 
Qed.  
              
Theorem handler_correct_fail : 
  forall opcode vls pcl c m raddr s i,
  forall (INPUT: cache_hit c (opCodeToZ opcode) (labsToZs vls) (labToZ pcl))
         (RULE: apply_rule (projT2 (get_rule opcode)) pcl vls = None),
    exists st,
    runsToEscape (CState c m handler i (CRet raddr false false::s) (0,handlerTag) true)
                 (CState c m handler i st (-1,handlerTag) true).
Proof.
  intros.   
  edestruct (faultHandler_specEscape_None get_rule opcode vls pcl c) with (raddr := (0,0))
      as [stk1 [cache1 [pc1 [priv1 [[P1 P2] [P3 P4]]]]]]; eauto. 
   eapply init_enough; eauto. 
   eapply code_at_id. 
   inv P3. eexists. eauto.
Qed.

End HandlerCorrect.

End TMU.
