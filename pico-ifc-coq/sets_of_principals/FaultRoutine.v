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
Require Import CodeSpecs. 
Require Import CodeTriples.
Require Import CodeGen.

Section TMU. 

Open Local Scope Z_scope.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}
        {SysTable : syscall_table T}
        {WFCLatt: WfConcreteLattice T Latt CLatt SysTable}. 

Notation HT := (HT SysTable).
Notation HTEscape := (HTEscape SysTable).

(* --------------------- TMU Fault Handler code ------------------------------ *)

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

Fixpoint genScond {n:nat} (s: rule_cond n) : code :=
  match s with
  | A_True => genTrue
  | A_False => genFalse
  | A_LE e1 e2 => genExpr e2 ++ genExpr e1 ++ genFlows
  | A_And s1 s2 => genScond s2 ++ genScond s1 ++ genAnd 
  | A_Or s1 s2 => genScond s2 ++ genScond s1 ++ genOr 
  end.

Definition genApplyRule {n:nat} (am:AllowModify n): code :=
  ite (genScond (allow am))
      (some (genExpr (labResPC am) ++ (genExpr (labRes am)))) none.

Definition genCheckOp (op:OpCode): code :=
  genTestEqual (push (opCodeToZ op)) (loadFrom addrOpLabel).

Section FaultHandler.

Definition fetch_rule_impl_type: Type := 
  forall (opcode:OpCode),  {n:nat & AllowModify n}.

Variable fetch_rule_impl: fetch_rule_impl_type.

Definition opcodes := [OpNoop; OpAdd; OpSub; OpPush; 
                       OpSwap; OpDup; OpPop;
                       OpLoad; OpStore; OpJump; OpBranchNZ; OpCall; 
                       OpRet; OpVRet; OpOutput].

Definition genApplyRule' op := genApplyRule (projT2 (fetch_rule_impl op)).

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

(* ================================================================ *)
(* Fault-handler Code Specifications                                *)

(* Connecting vectors of labels to triples of tags. *)

Section Glue.

Import Vector.VectorNotations.

Local Open Scope nat_scope.

Definition nth_labToZ {n:nat} (vls: Vector.t T n) (s:nat) : Z -> memory -> Prop :=
  fun z m => 
    match le_lt_dec n s with
      | left _ => z = dontCare
      | right p => labToZ (Vector.nth_order vls p) z m
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

Lemma nth_order_valid: forall (n:nat) (vls: Vector.t T n) p m,
  forall (lt: p < n),
    forall z, 
      nth_labToZ vls p z m ->
      labToZ (Vector.nth_order vls lt) z m.
Proof.
  intros.
  unfold nth_labToZ in *.
  destruct (le_lt_dec n p).
  false; omega.
  erewrite nth_order_proof_irrel; eauto.
Qed.

Lemma nth_order_complete: forall (n:nat) (vls: Vector.t T n) p m,
  forall (lt: p < n),
    forall z, 
      labToZ (Vector.nth_order vls lt) z m ->
      nth_labToZ vls p z m.
Proof.
  intros.
  unfold nth_labToZ in *.
  destruct (le_lt_dec n p).
  false; omega.
  erewrite nth_order_proof_irrel; eauto.
Qed.

Definition labsToZs {n:nat} (vls :Vector.t T n) (m: memory) : (Z * Z * Z) -> Prop :=
fun z0z1z2 =>
  let '(z0,z1,z2) := z0z1z2 in 
  nth_labToZ vls 0 z0 m /\
  nth_labToZ vls 1 z1 m /\
  nth_labToZ vls 2 z2 m.

End Glue.

Section TMUSpecs.

Definition handlerLabel := bot. 

Definition handler_initial_mem_matches 
           (opcode: Z)
           (tag1: Z) (tag2: Z) (tag3: Z) (pctag: Z) 
           (m: memory) : Prop := 
     (index_list_Z addrOpLabel m = Some (opcode,handlerTag))
  /\ (index_list_Z addrTag1 m = Some (tag1,handlerTag))
  /\ (index_list_Z addrTag2 m = Some (tag2,handlerTag))
  /\ (index_list_Z addrTag3 m = Some (tag3,handlerTag))
  /\ (index_list_Z addrTagPC m = Some (pctag,handlerTag))
.

(* APT: Just a little sanity check that these definitions are somewhat coherent. *)
Lemma init_init: forall (m:memory)  op ts tpc, 
                   cache_hit m op ts tpc ->
                   let '(l1,l2,l3) := ts in
                   handler_initial_mem_matches op l1 l2 l3 tpc m.
Proof.
  intros.
  inv H. inv OP. inv TAG1. inv TAG2. inv TAG3. inv TAGPC. 
  econstructor; jauto.
Qed.

(* Connecting to the definition used in ConcreteMachine.v *)
Lemma init_enough: forall {n} (vls:Vector.t T n) m opcode pcl z0 z1 z2 zpc,
                   forall (Hvls: labsToZs vls m (z0,z1,z2))
                          (Hpcl: labToZ pcl zpc m),
    cache_hit m (opCodeToZ opcode) (z0,z1,z2) zpc ->
    handler_initial_mem_matches (opCodeToZ opcode) z0 z1 z2 zpc m.
Proof.
  intros. destruct Hvls as [Hz0 [Hz1 Hz2]]. 
  inv H. inv UNPACK. inv OP. inv TAG1. inv TAG2. inv TAG3. inv TAGPC. 
  econstructor; jauto.
Qed.


Variable fetch_rule_impl: fetch_rule_impl_type.
Variable opcode: OpCode.
Let n := projT1 (fetch_rule_impl opcode).
Let am := projT2 (fetch_rule_impl opcode).
Variable vls: Vector.t T n.
Variable pcl: T.
Let eval_var := mk_eval_var vls pcl.

Definition INIT_MEM : memory -> Prop := 
  fun m0 =>  exists z0 z1 z2 zpc zr zrpc tr trpc,
               nth_labToZ vls 0 z0 m0
               /\ nth_labToZ vls 1 z1 m0
               /\ nth_labToZ vls 2 z2 m0
               /\ labToZ pcl zpc m0
               /\ handler_initial_mem_matches (opCodeToZ opcode) 
                                              z0 z1 z2 zpc
                                              m0
               /\ index_list_Z addrTagResPC m0 = Some (zrpc,trpc)
               /\ index_list_Z addrTagRes m0 = Some (zr,tr).

Ltac destruct_INIT_MEM :=
  match goal with 
      | [H: INIT_MEM _ |- _ ] =>
        destruct H as [z0 [z1 [z2 [zpc [zr [zrpc [tr [trpc [Hz0 [Hz1 [Hz2 [Hpc [Hhandler [? ?]]]]]]]]]]]]]]
  end.

Variable m0: memory.
Hypothesis initial_m0: INIT_MEM m0.

Lemma extension_comp_nth_labToZ : forall m1 m2 (n m:nat) (vls: Vector.t T n) z,
    nth_labToZ vls m z m1 ->
    extends m1 m2 ->
    mem_def_on_cache m1 ->
    nth_labToZ vls m z m2.
Proof.
  unfold nth_labToZ; intros.
  destruct (le_lt_dec n0 m); eauto.
  eapply labToZ_extension_comp; eauto.
Qed.

Lemma extension_comp_INIT_MEM : forall m1 m2, 
    INIT_MEM m1 -> 
    extends m1 m2 -> 
    INIT_MEM m2.
Proof.
  intros.
  destruct_INIT_MEM. inv Hhandler. intuition.
  exists z0; exists z1 ; exists z2 ; exists zpc; do 2 eexists.
  assert (Hm1: mem_def_on_cache m1). 
  econstructor; eauto. do 6 eexists; eauto. intuition; repeat econstructor; eauto.
  do 2 eexists; intuition; eauto using extension_comp_nth_labToZ.
  eapply (labToZ_extension_comp m1 m2); eauto.
  econstructor; intuition ; eauto.
Qed.  

Lemma INIT_MEM_def_on_cache: forall m, INIT_MEM m -> mem_def_on_cache m.
Proof.
  econstructor; eauto.
  destruct_INIT_MEM. inv Hhandler; intuition. 
  do 6 eexists; eauto. repeat (econstructor; eauto); eauto. 
Qed.
    
(* genVar is only loading things on the stack, so no need 
   of the memory extension hyp of I *)
Lemma genVar_spec:
  forall v l,
    eval_var v = l ->
    forall I,
      HT (genVar v)
         (fun m s => extends m0 m /\ I m s)
         (fun m s => 
            match s with 
              | (z,t) ::: tl => extends m0 m /\ 
                                labToZ l z m /\ 
                                t = handlerTag /\ I m tl
              | _ => False 
            end).
Proof.
  intros v l Heval_var I. 
  destruct_INIT_MEM. 
  assert (Hmem0: mem_def_on_cache m0).
  { econstructor; eauto. 
    inv Hhandler. 
    do 6 eexists; eauto.
    intuition; repeat (econstructor; eauto).
  }
  inv Hhandler. intuition. 
  case_eq v; intros; subst; simpl;
  match goal with 
      | [HH: read_m ?addr _ = Some (?zz,?tag) |- _ ] =>
        solve [
        eapply HT_strengthen_premise 
        with (P:=(fun m1 s0 => read_m addr m1 = Some (zz, tag) /\ 
                               ((fun m s => extends m0 m /\ I m s) m1 s0)));
        try solve [simpl; intros ? ? [? ?]; subst; eauto];
        eapply HT_weaken_conclusion;
        try eapply (loadFrom_spec_I SysTable addr zz tag (fun m s => extends m0 m /\ I m s));
        try (simpl; intros;
             destruct s; intuition; 
             (destruct c; intuition); 
             (destruct a; intuition);
             subst; eauto using labToZ_extension_comp, nth_order_valid)]
  end.
Qed.                      

Hint Resolve  extension_comp_INIT_MEM INIT_MEM_def_on_cache.

Lemma genExpr_spec: forall (e: rule_expr n),
  forall l,
    eval_expr eval_var e = l ->
    forall I
           (Hext: extension_comp I),
      HT   (genExpr e)
           (fun m s => extends m0 m /\ I m s)
           (fun m s => match s with
                         | (z, t) ::: tl => I m tl /\ labToZ l z m  /\
                                            t = handlerTag /\ 
                                            extends m0 m /\ INIT_MEM m
                         | _ => False
                       end).
Proof.
  induction e; intros ? Heval_expr ? Hext;
  simpl; simpl in Heval_expr.
  subst l. 
  - eapply HT_weaken_conclusion. 
    eapply genBot_spec' ; eauto. 
    unfold extension_comp, extends in *; intuition ; eauto.
    go_match. 
    
  - eapply HT_weaken_conclusion.
    eapply genVar_spec; eauto.
    go_match.

  - eapply HT_compose.
    eapply IHe2; eauto.
  
    eapply HT_compose.
    eapply HT_strengthen_premise.
    eapply (IHe1 (eval_expr eval_var e1) (eq_refl _) 
                 (fun m s => 
                    match s with 
                      | (z,t):::tl => I m tl 
                        /\ labToZ (eval_expr eval_var e2) z m
                        /\ t = handlerTag /\ extends m0 m /\ INIT_MEM m
                      | _ => False
                    end)); eauto.
    unfold extension_comp, extends.
    destruct s; intuition.
    destruct c; intuition.
    destruct a. 
    intuition; subst; eauto using labToZ_extension_comp.
    go_match.  
    eapply HT_strengthen_premise.
    eapply HT_weaken_conclusion.
    eapply genJoin_spec'; eauto.
    go_match.  
    go_match. 
Qed.

Lemma genScond_spec: forall (c: rule_cond n),
  forall b,
    eval_cond eval_var c = b ->
    forall I (Hext: extension_comp I),
      HT   (genScond c)
           (fun m s => extends m0 m /\ I m s)
           (fun m s => match s with 
                           | (z,t):::tl => I m tl /\ boolToZ b = z /\
                                           t = handlerTag /\ extends m0 m /\ INIT_MEM m
                           | _ => False
                       end).
Proof.
  induction c; intros; simpl;
    try (simpl in H); subst.

  (* True *)
  eapply HT_weaken_conclusion.
  eapply push_spec_I. go_match.

  (* False *)
  eapply HT_weaken_conclusion.
  eapply push_spec_I. go_match.

  (* Flows *)
  eapply HT_compose.
  eapply genExpr_spec; eauto.

  eapply HT_compose.
  eapply HT_strengthen_premise; eauto.
  eapply (genExpr_spec r (eval_expr eval_var r) (eq_refl _)) 
  with 
  (I:= fun m s =>
         match s with
           | (z, t) ::: tl => I m tl /\ labToZ (eval_expr eval_var r0) z m /\ 
                              t = handlerTag /\ extends m0 m
           | _ => False
     end). 
    unfold extension_comp, extends; simpl. 
    intros.
    destruct s; intuition.
    destruct c; intuition.
    destruct a. 
    intuition; subst; eauto using labToZ_extension_comp.
    go_match.
  eapply HT_consequence.
  eapply (genFlows_spec' (eval_expr eval_var r) (eval_expr eval_var r0)
         (fun m s => extends m0 m /\ I m s)) ; eauto.
  unfold extension_comp, extends; simpl. intuition; eauto.
  go_match.
  go_match. 

  (* And *)
  eapply HT_compose.
  eapply IHc2; eauto.
  
  eapply HT_compose.
  eapply HT_strengthen_premise.
  eapply (IHc1 (eval_cond eval_var c1) (eq_refl _) 
                 (fun m s => 
                    match s with 
                      | (z,t):::tl => I m tl 
                        /\ boolToZ (eval_cond eval_var c2) = z 
                        /\ t = handlerTag /\ extends m0 m
                      | _ => False
                    end)); eauto.
  unfold extension_comp, extends; simpl.
  intuition; eauto. go_match.
    
  go_match.  
    
  eapply HT_consequence.
  eapply (genAnd_spec_I SysTable) with (I:= fun m s => extends m0 m /\ I m s) ; eauto.
  go_match. 
  go_match. 

    (* OR *)
  eapply HT_compose.
  eapply IHc2; eauto.
  
  eapply HT_compose.
  eapply HT_strengthen_premise.
  eapply (IHc1 (eval_cond eval_var c1) (eq_refl _) 
                 (fun m s => 
                    match s with 
                      | (z,t):::tl => I m tl 
                        /\ boolToZ (eval_cond eval_var c2) = z 
                        /\ t = handlerTag /\ extends m0 m
                      | _ => False
                    end)); eauto.
  unfold extension_comp, extends; simpl.
  intuition; eauto. go_match.
  go_match.  
  
  eapply HT_consequence.
  eapply (genOr_spec_I SysTable) with (I:= fun m s => extends m0 m /\ I m s) ; eauto.
  go_match. 
  go_match. 
Qed.

Lemma genApplyRule_spec_Some:
  forall l1 l2,
    apply_rule am pcl vls = Some (l1, l2) ->
    forall I (Hext: extension_comp I),
      HT   (genApplyRule am)
           (fun m s => extends m0 m /\ I m s)
           (fun m s => match s with 
                           | (some1, t1) ::: (zr, t3) ::: (zrpc, t4) ::: tl =>
                             1 = some1 (* [Some (...)] *)
                             /\ labToZ l1 zrpc m /\ labToZ l2 zr m
                             /\ t1 = handlerTag 
                             /\ t3 = handlerTag /\ t4 = handlerTag 
                             /\ extends m0 m /\ I m tl
                           | _ => False
                       end). 
Proof.
  introv Happly. 
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly. 
  inv  Happly. intros I Hext.
  
  - eapply (ite_spec_specialized_I' SysTable (boolToZ true)); eauto. 
    
    + eapply HT_weaken_conclusion.
      eapply (genScond_spec (allow am) true H I); eauto.
      go_match.
    
    + intros.  
      eapply HT_weaken_conclusion.
      eapply some_spec_I.
      
      eapply HT_compose.
      eapply genExpr_spec with (I:= I); eauto.
      
      eapply HT_strengthen_premise.
      eapply genExpr_spec with 
      (I:= fun m s => match s with 
                        | (z, t) ::: tl0 =>
                          I m tl0 
                          /\ labToZ (eval_expr eval_var (labResPC am)) z m
                          /\ t = handlerTag /\ extends m0 m
                        | _ => False 
                      end); eauto.
      unfold extension_comp, extends in *.
      simpl. intuition. go_match. eauto using labToZ_extension_comp.
      go_match. 
      go_match. 
    + intros; false; omega.  
Qed.

Lemma genApplyRule_spec_None:
    apply_rule am pcl vls  = None ->
    forall I (Hext: extension_comp I),
      HT   (genApplyRule am)
           (fun m s => extends m0 m /\ I m s)
           (fun m s => match s with 
                         | (none1, t1) :::  tl =>
                           0 = none1  (* [None] *)
                           /\ t1 = handlerTag 
                           /\ extends m0 m /\ I m tl
                         | _ => False
                       end). 
Proof.
  introv Happly Hext. 
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.
  
  eapply ite_spec_specialized_I' with (v:=boolToZ false); eauto; intros. 
  eapply HT_weaken_conclusion.
  eapply genScond_spec; auto. unfold eval_var, n. 
  rewrite H.
  go_match.
  unfold boolToZ in *; false; try omega.

  eapply HT_weaken_conclusion.
  eapply (push_spec_I SysTable 0); eauto.
  go_match.
Qed.

Definition listify_apply_rule (ar: option (T * T))
                              (s0: stack) (zr zpc: Z) : stack -> Prop :=
  match ar with
  | None              => fun s => s = CData (0, handlerTag) :: s0
  | Some (lpc,    lr) => fun s => s = CData (1, handlerTag)   ::
                                      CData (zr, handlerTag)  ::
                                      CData (zpc, handlerTag) :: s0
  end.

Definition labToZ_rule_res (ar: option (T * T)) (zr zpc: Z) m : Prop :=
  match ar with
  | None           => True
  | Some (lpc, lr) => labToZ lr zr m /\ labToZ lpc zpc m
  end.

Lemma genApplyRule_spec:
  forall ar,
    apply_rule am pcl vls = ar ->
    forall I (Hext: extension_comp I),
      HT   (genApplyRule am)
           (fun m s => extends m0 m /\ I m s)
           (fun m s => extends m0 m /\
                       exists s0 zr zrpc,
                       labToZ_rule_res ar zr zrpc m /\
                       listify_apply_rule ar s0 zr zrpc s /\
                       I m s0).
Proof.
  intros. 
  unfold listify_apply_rule, labToZ_rule_res. 
  case_eq ar ; [intros [r rpc] | intros rpc] ; intros ; subst.
  - eapply HT_weaken_conclusion. 
    eapply (genApplyRule_spec_Some r rpc H0 I); eauto.
    go_match.
    do 3 eexists; eauto.
  - eapply HT_weaken_conclusion. 
    eapply genApplyRule_spec_None; eauto.
    go_match. eexists. eexists 0. eexists 0.
    eauto.
Qed.

Lemma genApplyRule_spec_GT_ext:
  forall ar,
    apply_rule am pcl vls = ar ->
    forall (I:HProp) (Hext: extension_comp I),
      GT_ext SysTable (genApplyRule am)
         (fun m s => extends m0 m /\ I m s)
         (fun m0' s0 m s => extends m0 m0' /\ extends m0' m /\
                            exists zr zrpc,
                              labToZ_rule_res ar zr zrpc m /\
                              listify_apply_rule ar s0 zr zrpc s /\
                              I m s0). 
Proof.
  unfold GT_ext; intros.
  eapply HT_consequence.
  eapply  (genApplyRule_spec ar H (fun m s => extends m0 m1 /\ 
                                              extends m1 m /\ 
                                              s = s0 /\ I m s)); eauto. 
  unfold extension_comp; eauto.
  unfold extends in *; intuition ; eauto.  
  go_match. intuition; substs; eauto.
  unfold extends. auto. 
  simpl. intros m s [Hm [s1 [zr [zrpc [Har Hlist]]]]].
  intuition. substs; eauto. 
Qed.


Lemma genCheckOp_spec_HT_ext:
  forall opcode' I (Hext: extension_comp I),
    HT (genCheckOp opcode')
       (fun m s => extends m0 m /\ I m s)
       (fun m s => match s with 
                       | (z,t):::tl =>
                         extends m0 m /\
                         boolToZ (opCodeToZ opcode' =? opCodeToZ opcode) = z /\
                         t = handlerTag /\
                         I m tl
                       | _ => False
                   end).
Proof.
  destruct_INIT_MEM. 
  inv Hhandler. intuition.
  unfold genCheckOp.
  eapply genTestEqual_spec_I. intros I' HextI'.
  eapply HT_strengthen_premise.
  eapply HT_weaken_conclusion.
  eapply (push_spec_I SysTable) with (I:= fun m s => extends m0 m /\ I' m s).
  go_match.
  go_match. intuition. 
  intros I' HextI'.
  eapply HT_strengthen_premise.
  eapply HT_weaken_conclusion.
  eapply (loadFrom_spec_I SysTable) with (I:= fun m s => extends m0 m /\ I' m s).
  go_match.
  go_match. intuition. eauto.
Qed.

Lemma genCheckOp_spec_GT_ext:
  forall opcode' I (Hext: extension_comp I),
    GT_ext SysTable (genCheckOp opcode')
       (fun m s => extends m0 m /\ I m s)
       (fun m0' s0 m s => extends m0 m0' /\ extends m0' m /\
                          s = (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode)
                               ,handlerTag) ::: s0
                          /\ I m s0).
Proof.
  unfold GT_ext; intros. 
  eapply HT_weaken_conclusion.
  eapply HT_strengthen_premise.
  eapply genCheckOp_spec_HT_ext with (I:= fun m s => extends m0 m1 /\ 
                                                 extends m1 m /\ 
                                                 I m s /\ s = s0).
  unfold extension_comp, extends ; simpl ; eauto.
  simpl; intuition (subst; eauto).
  simpl. intuition; substs; auto. 
  unfold extends in * ; eauto.
  unfold extends in * ; eauto.  
  simpl. go_match.
Qed.

End TMUSpecs.

Section FaultHandlerSpec.

Variable ar: option (T * T).

Variable fetch_rule_impl: fetch_rule_impl_type.
Variable (opcode: OpCode).  
Let n := projT1 (fetch_rule_impl opcode).
Let am := projT2 (fetch_rule_impl opcode).

Variable (vls: Vector.t T n).
Variable (pcl: T).

Let eval_var := mk_eval_var vls pcl.

Hypothesis H_apply_rule: apply_rule am pcl vls = ar.


(* Don't really need to specify [Qnil] since it will never run *)
Definition Qnil: GProp := fun m0' s0 m s => True.
Definition genV: OpCode -> HFun :=
  fun i _ _  => boolToZ (opCodeToZ i =? opCodeToZ opcode).
Definition genC: OpCode -> code := genCheckOp.
Definition genB: OpCode -> code := genApplyRule' fetch_rule_impl.
Definition genQ: HProp -> OpCode -> GProp :=
         (fun I i m0' s0 m s => extends m0' m /\
                                exists zr zrpc,              
                                  labToZ_rule_res ar zr zrpc m /\
                                  listify_apply_rule ar s0 zr zrpc s /\ I m s0).

Let INIT_MEM := INIT_MEM fetch_rule_impl opcode vls pcl.

Variable m0 : memory.
Hypothesis INIT_MEM0: INIT_MEM m0.

Lemma genCheckOp_spec_GT_push_v_ext:
  forall opcode' I (Hext: extension_comp I),
    GT_push_v_ext SysTable (genC opcode')
                  (fun m s => extends m0 m /\ I m s)
                  (genV opcode'). 
Proof. 
  intros; eapply GT_consequence'_ext. 
  eapply genCheckOp_spec_GT_ext with (I:= fun m s => extends m0 m /\ I m s); eauto.
  unfold extension_comp, extends in *; intuition ; eauto.
  intuition. 
  simpl. intuition; auto.
Qed.

Lemma opCodeToZ_inj: forall opcode opcode',
  (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode) <> 0) ->
  opcode' = opcode.
Proof.
  intros o o'.
  destruct o; destruct o'; simpl; solve [ auto | intros; false; omega ].
Qed.

Lemma genApplyRule'_spec_GT_guard_v_ext: 
  forall opcode' I (Hext: extension_comp I),
    GT_guard_v_ext SysTable (genB opcode')
               (fun m s => extends m0 m /\ I m s)
               (genV opcode')
               (genQ I opcode').
Proof.
  intros.
  cases (dec_eq_OpCode opcode' opcode) as Eq; clear Eq. substs.
  - eapply GT_consequence'_ext.
    unfold genB, genApplyRule'. 
    eapply genApplyRule_spec_GT_ext  ; eauto.
    intuition.
    simpl. intuition.
    econstructor; eauto.

  - unfold GT_guard_v_ext, GT_ext, CodeTriples.HT.
    intros.
    unfold genV in *.
    pose (opCodeToZ_inj opcode opcode').
    false; intuition. 
Qed. 

Lemma H_indexed_hyps: forall (I:HProp) (Hext: extension_comp I), 
                        indexed_hyps_ext SysTable _ genC genB (genQ I)
                        genV (fun m s => extends m0 m /\ I m s) opcodes.
Proof.
  unfold indexed_hyps_ext; simpl; 
  intuition ; try (solve
    [ (eapply GT_consequence'_ext; eauto);
    try solve [(eapply genCheckOp_spec_GT_push_v_ext; eauto)];
    try (simpl ; intuition ; subst ; iauto)
    | eapply genApplyRule'_spec_GT_guard_v_ext; eauto ]). 
Qed.

End FaultHandlerSpec.

Variable ar: option (T * T).

Variable fetch_rule_impl: fetch_rule_impl_type.
Variable (opcode: OpCode).  
Let n := projT1 (fetch_rule_impl opcode).
Let am := projT2 (fetch_rule_impl opcode).

Variable (vls: Vector.t T n).
Variable (pcl: T).

Let eval_var := mk_eval_var vls pcl.

Hypothesis H_apply_rule: apply_rule am pcl vls = ar.
Let INIT_MEM := INIT_MEM fetch_rule_impl opcode vls pcl.

Lemma genComputeResults_spec_GT_ext: forall I (Hext: extension_comp I)
                                       m0 (INIT_MEM0: INIT_MEM m0),
    GT_ext SysTable (genComputeResults fetch_rule_impl)
       (fun m s => extends m0 m /\ I m s)
       (fun m0' s0 m s => extends m0 m0' /\ extends m0' m /\
                          exists zr zpc,
                            labToZ_rule_res ar zr zpc m /\
                            listify_apply_rule ar s0 zr zpc s /\ I m s0).
Proof.
  intros. 
  unfold genComputeResults. 
  eapply GT_consequence'_ext.
  eapply indexed_cases_spec_ext with 
  (Qnil:= Qnil) 
  (genV:= genV opcode)
  (P:= fun m s => extends m0 m /\ I m s)
  (genQ:= genQ ar I).
  - Case "default case that we never reach".
    unfold GT_ext; intros.
    eapply HT_consequence.
    eapply (nop_spec_I SysTable) with (I:= fun m s => extends m1 m /\ I m s /\ I m1 s); eauto.
    intros. intuition; subst. 
    unfold extends in * ; eauto.
    eauto.
    unfold Qnil; iauto.
  - eapply (H_indexed_hyps ar fetch_rule_impl opcode vls pcl H_apply_rule m0 INIT_MEM0  I); auto.
  - simpl. iauto.
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

Lemma genComputeResults_spec: forall I s0 m0 (INIT_MEM0: INIT_MEM m0),
    forall (Hext: extension_comp I),
      HT   (genComputeResults fetch_rule_impl)
           (fun m s => extends m0 m /\ s = s0 /\ I m0 s /\ I m s)
           (fun m s => extends m0 m /\
                       exists zr zpc, 
                         labToZ_rule_res ar zr zpc m /\         
                         listify_apply_rule ar s0 zr zpc s /\ I m s0).
Proof.
  intros.
  eapply HT_consequence.  
  eapply (genComputeResults_spec_GT_ext I Hext m0); eauto.
  simpl.
  
  intros; intuition; substs; auto.
  unfold extends; eauto. auto. 
  unfold extends; eauto. 
  intros; intuition; intuition. 
Qed.

(* trying in WP wtyle *)
Lemma storeAt_spec_wp': forall a Q,
  HT (storeAt a)
     (fun m0 s0 => exists vl s m, s0 = vl ::: s /\
                               upd_m a vl m0 = Some m /\
                               Q m s)
     Q.
Proof.
  intros.
  eapply HT_compose_flip.
  eapply store_spec_wp'; eauto.
  unfold push. 
  eapply HT_strengthen_premise.
  eapply push_spec_wp.

  intuition; eauto. destruct H as [vl [s0 [m0 Hint]]]. intuition; substs.
  do 5 eexists; intuition; eauto.
Qed.

Lemma genStoreResults_spec_Some: forall Q,
  forall lr lpc,
    ar = Some (lpc,lr) ->
      HT genStoreResults
         (fun m s => exists s0 zr zpc,
            labToZ_rule_res ar zr zpc m /\
            listify_apply_rule ar s0 zr zpc s /\
            valid_address addrTagRes m /\
            valid_address addrTagResPC m /\
            exists m' m'',
              (upd_m addrTagRes (zr,handlerTag) m = Some m' 
               /\ upd_m addrTagResPC (zpc,handlerTag) m' = Some m''
               /\ labToZ_rule_res ar zr zpc m''
               /\ Q m'' ((1,handlerTag):::s0)))
         Q
.
Proof.
  introv Har_eq; intros.
  unfold listify_apply_rule.
  rewrite Har_eq.
  unfold genStoreResults.
  eapply HT_strengthen_premise. 
  eapply ifNZ_spec_existential. 
  eapply HT_compose_flip.
  eapply HT_compose_flip. 
  eapply genTrue_spec_wp; eauto. 
  eapply storeAt_spec_wp'.
  eapply storeAt_spec_wp'. 
  eapply genFalse_spec_wp.

  intros. destruct H as [s0 [zr [zpc Hint]]]. intuition. 
  destruct H4 as [m' [m'' Hint]]. intuition.
  subst.

  exists 1. exists handlerTag. exists ((zr, handlerTag) ::: (zpc, handlerTag) ::: s0).
  split; eauto. 
  split. intros.
  
  do 3 eexists ; eauto. intuition; subst; eauto.
  do 3 eexists ; eauto. 
  intuition.
Qed.

Lemma genStoreResults_spec_None: forall Q: memory -> stack -> Prop,
  ar = None ->
    HT genStoreResults
       (fun m s => exists s0 zr zpc, 
                     labToZ_rule_res ar zr zpc m /\
                     listify_apply_rule ar s0 zr zpc s /\
                     (forall m0, 
                       extends m m0 -> Q m0 ((0,handlerTag) ::: s0)))
       Q.
Proof.
  introv Har_eq; intros.
  unfold listify_apply_rule.
  rewrite Har_eq.
  unfold genStoreResults.

  eapply HT_strengthen_premise.
  eapply ifNZ_spec_existential.

  
  eapply HT_compose_flip. 
  eapply HT_compose_flip. 
  eapply genTrue_spec_wp; eauto. 
  eapply storeAt_spec_wp'.
  eapply storeAt_spec_wp'. 
  eapply genFalse_spec_wp.

  intros. destruct H as [s0 [zr [zpc Hint]]]. intuition. substs.
  exists 0. exists handlerTag. exists s0.
  split; eauto. intuition. 
  eapply H2; eauto. 
  unfold extends; eauto. 
Qed.


(* This had to be relaxed as well. m' extends m, except for the update
of zr and zpc *)

Definition handler_final_mem_matches (lrpc lr: T) (m m': memory): Z -> Z -> Prop :=
  fun zpc zr =>
    exists m_ext, 
      extends m m_ext /\
      labToZ lrpc zpc m' /\
      labToZ lr zr m' /\
      cache_hit_read m' zr zpc /\
      update_cache_spec_rvec m_ext m'. (* Nothing else changed since the extension *)

Lemma genError_specEscape: forall raddr (P: memory -> stack -> Prop),
  HTEscape raddr genError
           P
           (fun m s => (P m s , Failure)).
Proof.
  intros.
  unfold genError.
  eapply HTEscape_compose.
  - eapply push_spec'.
  - eapply HTEscape_strengthen_premise.
    + eapply jump_specEscape_Failure.
    + intuition.
      cases s; subst.
      * rewrite hd_error_nil in *; false.
      * rewrite hd_error_cons in *.
        inversion H0; subst. eauto.
Qed.

Definition genFaultHandlerReturn: code := ifNZ [Ret] genError.

Lemma genFaultHandlerReturn_specEscape_Some: forall raddr (Q: memory -> stack -> Prop),
  HTEscape raddr genFaultHandlerReturn
           (fun m s =>
              exists s0,
              s = (1, handlerTag) ::: CRet raddr false false :: s0 /\
              Q m s0)
           (fun m s  => (Q m s, Success)).
Proof.
  intros.
  unfold genFaultHandlerReturn.
  eapply HTEscape_strengthen_premise.
  - eapply ifNZ_specEscape with (v:=1) (Pf:=fun m s => True); intros.
    eapply ret_specEscape.
    false.
  - subst.
    intuition. destruct H as [s0 Hint]. intuition.
    substs. jauto_set_goal; eauto.
Qed.

Lemma genFaultHandlerReturn_specEscape_None: forall raddr s0 m0,
 HTEscape raddr genFaultHandlerReturn
   (fun m s => (extends m0 m /\ s = (0, handlerTag) ::: s0))
   (fun m s => (extends m0 m /\ s = s0, Failure)).
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

(*
Lemma extends_valid_address: forall m m' a, 
                               valid_address a m ->
                               extends m m' ->
                               valid_address a m'.
Proof.
  intros.
  exploit valid_read; eauto. intros [v Hread].
  unfold valid_address, extends in * ; intros.
  intuition.
  exploit H0; eauto. intros.
  eapply index_list_Z_valid; eauto.
Qed.

*)
  
Lemma faultHandler_specEscape_Some: forall syscode raddr lr lpc m0,
  INIT_MEM m0 ->
  valid_address addrTagRes m0 ->
  valid_address addrTagResPC m0 ->
  ar = Some (lpc, lr) ->
  forall s0,
    HTEscape raddr ((faultHandler fetch_rule_impl)++syscode)
             (fun m s => m = m0 /\
                         s = (CRet raddr false false::s0))
             (fun m s => ( exists zr zpc, 
                             s = s0 /\ 
                             handler_final_mem_matches lpc lr m0 m zpc zr
                         , Success )).
Proof.
  intros.
  eapply HTEscape_append.
  unfold faultHandler. 
  
  eapply HTEscape_compose_flip.
  eapply HTEscape_compose_flip.

  eapply genFaultHandlerReturn_specEscape_Some ; eauto.
  eapply genStoreResults_spec_Some; eauto.
  eapply HT_consequence. 
  eapply genComputeResults_spec with 
    (I := fun m s => True)
    (m0 := m0)
    (s0 := CRet raddr false false :: s0)
  ; eauto.
  unfold extension_comp; eauto. 
  intros. intuition. substs. unfold extends; eauto. 
  simpl. intros. intuition.
  destruct H5 as [zr [zpc Hint]]. intuition.
  exists (CRet raddr false false :: s0).
  exists zr ; exists zpc.
  intuition; eauto using extends_valid_address.
  
  assert (Hm'm'': 
            exists m' m'', 
              upd_m addrTagRes (zr, handlerTag) m = Some m' /\
              upd_m addrTagResPC (zpc, handlerTag) m' = Some m'').
  { 
   exploit (extends_valid_address m0 m addrTagRes); eauto. intros HvalidRes.
   exploit (extends_valid_address m0 m addrTagResPC); eauto. intros HvalidResPC.
   eapply (valid_store addrTagRes (zr,handlerTag)) in HvalidRes.
   destruct HvalidRes as [m' ?].   
   eapply valid_address_upd with (a:= addrTagResPC) in HvalidResPC; eauto.
   eapply valid_store in HvalidResPC.
   destruct HvalidResPC as [m'' ?]; eauto.
  }

  destruct Hm'm'' as [m' [m'' [Hm' Hm'']]].
  assert (Hup: mem_eq_except_cache m m''); eauto. 
     unfold mem_eq_except_cache.
     split. eapply INIT_MEM_def_on_cache; eauto using extension_comp_INIT_MEM.
     intros. 
     eapply update_list_Z_spec2 in Hm'; eauto. 
     eapply update_list_Z_spec2 in Hm''; eauto. 
     unfold Atom in *; congruence.
  do 2 eexists ; intuition; eauto. 
  {  unfold labToZ_rule_res in *.
     rewrite H2 in *. intuition; eapply labToZ_cache; eauto.
  }     
  eexists; intuition; eauto.
  exists zr ; exists zpc ; intuition; eauto.
  exists m. intuition; eauto.
  {  unfold labToZ_rule_res in *.
     rewrite H2 in *. intuition; eapply labToZ_cache; eauto.
  }     
  {  unfold labToZ_rule_res in *.
     rewrite H2 in *. intuition; eapply labToZ_cache; eauto.
  }     
  { econstructor. 
    exploit update_list_Z_spec; eauto. move_to_top Hm''.
    exploit update_list_Z_spec; eauto. intros Hreadm' Hreadm''.
    erewrite update_list_Z_spec2 in Hreadm'; eauto.
    eapply tim_intro' with (t:= handlerTag); eauto.
    unfold addrTagResPC, addrTagRes; congruence.
    exploit update_list_Z_spec; eauto. 
    econstructor; eauto.
  }
  unfold update_cache_spec_rvec.
  intros; jauto_set_hyps; intros.
  eapply transitivity.
  eapply update_list_Z_spec2; eauto.
  eapply update_list_Z_spec2; eauto.
Qed.

Lemma faultHandler_specEscape_None: forall syscode raddr m0,
                                    forall (INIT_MEM0: INIT_MEM m0),
  ar = None -> 
  forall s0,
    HTEscape raddr ((faultHandler fetch_rule_impl)++syscode)
             (fun m s => m0  = m /\ s = s0)
             (fun m s => ((extends m0 m /\ s = s0)
                         , Failure)).
Proof. 
  intros.
  eapply HTEscape_append.
  unfold faultHandler. 
  eapply HTEscape_compose_flip.
  eapply HTEscape_compose_flip.
  eapply genFaultHandlerReturn_specEscape_None ; eauto.
  eapply genStoreResults_spec_None; eauto.
  eapply HT_consequence. 
  eapply genComputeResults_spec with 
    (I := fun m s => True)
    (m0 := m0)
    (s0 := s0)
  ; eauto.
  unfold extension_comp; eauto. 
  intros. intuition. 
  subst. unfold extends in *; intuition.
  simpl. intros. intuition.
  destruct H2 as [zr [zpc Hint]]. intuition.
  exists s0. exists zr ; exists zpc.
  intuition; eauto using extends_valid_address.
  unfold extends in *; intuition.
Qed.

End TMU.

Section HandlerCorrect.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}
        {SysTable : syscall_table T}
        {WFCLatt: WfConcreteLattice T Latt CLatt SysTable}. 

Variable get_rule : forall (opcode:OpCode), {n:nat & AllowModify n}.
Definition handler : list Instr := faultHandler get_rule.

Require Import ConcreteExecutions.

Theorem handler_correct_succeed :
  forall syscode opcode vls pcl c m raddr s i lr lpc z1 z2 z3 zpc,
  forall 
    (LABS: (labsToZs vls) c (z1, z2, z3))
    (LABPC: (labToZ pcl) zpc c)
    (INPUT: cache_hit c (opCodeToZ opcode) (z1,z2,z3) zpc)
    (RULE: apply_rule (projT2 (get_rule opcode)) pcl vls = Some (lpc,lr)),
    exists c' zr zrpc,
    runsToEscape SysTable
                 (CState c m (handler++syscode) i (CRet raddr false false::s) (0,handlerTag) true)
                 (CState c' m (handler++syscode) i s raddr false) /\
    handler_final_mem_matches lpc lr c c' zrpc zr.
Proof.
 intros.
  assert (valid_address addrTagRes c).
    inv INPUT. inv TAGR. eapply index_list_Z_valid; eauto. 
  assert (valid_address addrTagResPC c).
    inv INPUT. inv TAGRPC. eapply index_list_Z_valid; eauto.
  edestruct (faultHandler_specEscape_Some (Some (lpc,lr)) _ opcode vls pcl RULE syscode raddr lr lpc c) 
      as [stk1 HH]; eauto. 
  exploit (@init_enough _ _ _ _ _ (projT1 (get_rule opcode)) vls); eauto. intros Hmem. 
  exists z1; exists z2 ; exists z3 ; exists zpc. 
  inv INPUT. 
  inv LABS; intuition ; eauto; 
  repeat match goal with 
      | [H: tag_in_mem' _ _ _ |- _ ] => inv H
      | [H: tag_in_mem _ _ _ |- _ ] => inv H
  end; do 4 eexists; intuition; eauto. 
  apply code_at_id. 
  destruct HH as [cache1 [pc1 [priv1 [[zr [zpc' [P1 P2]]] [P3 P4]]]]].
  subst. inv P3.
  exists cache1;  exists zr; exists zpc'.
  split; auto.
  eapply P4. 
Qed.  
              
Theorem handler_correct_fail : 
  forall syscode opcode vls pcl c m raddr s i z1 z2 z3 zpc,
  forall (LABS: (labsToZs vls) c (z1, z2, z3))
         (LABPC: (labToZ pcl) zpc c)
         (INPUT: cache_hit c (opCodeToZ opcode) (z1,z2,z3) zpc)
         (RULE: apply_rule (projT2 (get_rule opcode)) pcl vls = None),
    exists st c',
      runsToEscape SysTable
                   (CState c m (handler++syscode) i (CRet raddr false false::s) (0,handlerTag) true)
                   (CState c' m (handler++syscode) i st (-1,handlerTag) true) /\
    extends c c'.
Proof.
intros.
  edestruct (faultHandler_specEscape_None (SysTable:=SysTable) None _ opcode vls pcl RULE syscode raddr c) 
      as [stk1 HH]; eauto.   
  exploit (@init_enough _ _ _ _ _ (projT1 (get_rule opcode))); eauto. intros Hmem.
  exists z1; exists z2 ; exists z3 ; exists zpc.
  inv LABS; intuition ; auto. inv Hmem. inv INPUT.
  repeat match goal with 
      | [H: tag_in_mem' _ _ _ |- _ ] => inv H
      | [H: tag_in_mem _ _ _ |- _ ] => inv H
  end; do 4 eexists; intuition; eauto. econstructor; eauto.
  apply code_at_id. 
  destruct HH as [cache1 [pc1 [priv1 [[P1 P2] [P3 P4]]]]].
  substs. inv P3.
  eexists ; eexists; intuition; eauto. 
Qed.

End HandlerCorrect.
