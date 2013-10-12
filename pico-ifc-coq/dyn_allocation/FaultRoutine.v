Require Import ZArith.
Require Import List.
Require Import Utils.
Import ListNotations.
Require Vector.

Require Import LibTactics.
Require Import Instr Memory.
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

Notation Atom := (Atom (val privilege) privilege).
Notation memory := (Mem.t Atom privilege).
Notation PcAtom := (PcAtom (val privilege)).
Notation block := (block privilege).

Section TMU.

Open Local Scope Z_scope.

Variable cblock : block.
Variable stamp_cblock : Mem.stamp cblock = Kernel.
Variable table : CSysTable.
Variable labelCount : OpCode -> nat.
Variable fetch_rule : forall opcode, AllowModify (labelCount opcode).

Notation cget := (cget cblock).
Notation cache_hit_mem := (cache_hit_mem cblock).
Notation HT := (HT cblock table).
Notation GT := (GT cblock table).

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}
        {WFCLatt: WfConcreteLattice cblock table T Latt CLatt}.

Definition handler_final_mem_matches (lrpc lr: T) (m m': memory):
  val privilege -> val privilege -> Prop :=
  fun zpc zr =>
    exists m_ext,
      extends m m_ext /\
      labToVal lrpc zpc m' /\
      labToVal lr zr m' /\
      cache_hit_read_mem cblock m' zr zpc /\
      update_cache_spec_rvec cblock m_ext m'. (* Nothing else changed since the extension *)

Definition handler_spec_succeed handler : Prop :=
  forall syscode opcode vls pcl c raddr s i lr lpc z1 z2 z3 zpc,
  forall
    (CODE: code_at 0 syscode handler)
    (LABS: (labsToVals vls) c (z1, z2, z3))
    (LABPC: (labToVal pcl) zpc c)
    (INPUT: cache_hit_mem c (opCodeToZ opcode) (z1,z2,z3) zpc)
    (RULE: apply_rule (fetch_rule opcode) pcl vls = Some (lpc,lr)),
    exists c' zr zrpc,
    runsToEscape cblock table
                 (CState c syscode i (CRet raddr false false::s) (0,handlerTag) true)
                 (CState c' syscode i s raddr false) /\
    handler_final_mem_matches lpc lr c c' zrpc zr.

Definition handler_spec_fail handler : Prop :=
  forall syscode opcode vls pcl c raddr s i z1 z2 z3 zpc,
  forall (CODE: code_at 0 syscode handler)
         (LABS: (labsToVals vls) c (z1, z2, z3))
         (LABPC: (labToVal pcl) zpc c)
         (INPUT: cache_hit_mem c (opCodeToZ opcode) (z1,z2,z3) zpc)
         (RULE: apply_rule (fetch_rule opcode) pcl vls = None),
    exists st c',
      runsToEscape cblock table
                   (CState c syscode i (CRet raddr false false::s) (0,handlerTag) true)
                   (CState c' syscode i st (-1,handlerTag) true) /\
    extends c c'.

(* --------------------- TMU Fault Handler code ----------------------------------- *)

(* Compilation of rules *)

Definition genVar {n:nat} (l:LAB n) :=
  match l with
  (* NC: We assume the operand labels are stored at these memory
     addresses when the fault handler runs. *)
  | lab1 _ => loadFromCache addrTag1
  | lab2 _ => loadFromCache addrTag2
  | lab3 _ => loadFromCache addrTag3
  | labpc => loadFromCache addrTagPC
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
      (some
        (genExpr (labResPC am) ++
         genExpr (labRes am))
      )
      none.

Section FaultHandler.

Definition genCheckOp (op:OpCode): code :=
  genTestEqual (push (opCodeToZ op)) (loadFromCache addrOpLabel).

Definition opcodes :=
  [OpNoop;
   OpAdd;
   OpSub;
   OpEq;
   OpPush;
   OpPop;
   OpLoad;
   OpStore;
   OpJump;
   OpBranchNZ;
   OpCall;
   OpRet;
   OpVRet;
   OpOutput;
   OpDup;
   OpSwap;
   OpAlloc].

(* Just making sure the above is correct *)
Lemma opcodes_correct : forall op, In op opcodes.
Proof. intros []; compute; intuition. Qed.

Definition genApplyRule' op := genApplyRule (fetch_rule op).

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

(* NC: or

   ite (genComputeResults ++ genStoreResults)
        [Ret]
        genError.
*)

End FaultHandler.


(* ================================================================ *)
(* Fault-handler Code Specifications                                *)

(* Connecting vectors of labels to triples of tags. *)


Section TMUSpecs.

Inductive handler_initial_mem_matches
            (opcode: Z)
            (tag1 tag2 tag3 pctag : val privilege)
            (m: memory) : Prop :=
| hiim_intro : forall
                 (HOPCODE : value_on_cache cblock m addrOpLabel (Vint opcode))
                 (HTAG1 : value_on_cache cblock m addrTag1 tag1)
                 (HTAG2 : value_on_cache cblock m addrTag2 tag2)
                 (HTAG3 : value_on_cache cblock m addrTag3 tag3)
                 (HPC : value_on_cache cblock m addrTagPC pctag),
                 handler_initial_mem_matches opcode tag1 tag2 tag3 pctag m.
Hint Constructors handler_initial_mem_matches.

(* Connecting to the definition used in ConcreteMachine.v *)
Lemma init_enough: forall {n} (vls:Vector.t T n) m opcode pcl z0 z1 z2 zpc,
                   forall (Hvls: labsToVals vls m (z0,z1,z2))
                          (Hpcl: labToVal pcl zpc m),
    cache_hit_mem m (opCodeToZ opcode) (z0,z1,z2) zpc ->
    handler_initial_mem_matches (opCodeToZ opcode) z0 z1 z2 zpc m.
Proof.
  intros. destruct Hvls as [Hz0 [Hz1 Hz2]].
  unfold Concrete.cache_hit_mem,
         ConcreteMachine.cget in *.
  destruct (Mem.get_frame m cblock) as [cache|] eqn:E; inv H.
  inv UNPACK. inv OP. inv TAG1. inv TAG2. inv TAG3. inv TAGPC.
  econstructor; econstructor; unfold load; rewrite E; jauto.
Qed.

Variable (opcode: OpCode).
Let n := labelCount opcode.
Let am := fetch_rule opcode.
Variable (vls: Vector.t T n).
Variable (pcl: T).
Let eval_var := mk_eval_var vls pcl.

Inductive INIT_MEM (m0 : memory) : Prop :=
| IM_intro :
    forall z0 z1 z2 zpc zr zrpc
           (Hz0 : nth_labToVal vls 0 z0 m0)
           (Hz1 : nth_labToVal vls 1 z1 m0)
           (Hz2 : nth_labToVal vls 2 z2 m0)
           (Hpc : labToVal pcl zpc m0)
           (Hhandler : handler_initial_mem_matches (opCodeToZ opcode)
                                                   z0 z1 z2 zpc
                                                   m0),
      value_on_cache cblock m0 addrTagResPC zrpc ->
      value_on_cache cblock m0 addrTagRes zr ->
      INIT_MEM m0.
Hint Constructors INIT_MEM.

Variable (m0: memory).
Hypothesis initial_m0 : INIT_MEM m0.


Lemma extension_comp_value_on_cache :
  forall m1 m2 addr v,
    value_on_cache cblock m1 addr v ->
    extends m1 m2 ->
    value_on_cache cblock m2 addr v.
Proof.
  intros m1 m2 addr v H1 H2. inv H1.
  eapply extends_load in H; eauto.
  econstructor. eauto.
Qed.
Hint Resolve extension_comp_value_on_cache.

Lemma INIT_MEM_def_on_cache: forall m, INIT_MEM m -> mem_def_on_cache cblock m.
Proof.
  intros m H.
  destruct H. inv H.
  unfold load in *. unfold mem_def_on_cache.
  destruct (Mem.get_frame m cblock); inv H1; eauto.
Qed.

Lemma extension_comp_INIT_MEM : forall m1 m2,
    INIT_MEM m1 ->
    extends m1 m2 ->
    INIT_MEM m2.
Proof.
  intros.
  destruct H.
  inv Hhandler.
  econstructor; eauto 7 using extension_comp_nth_labToVal, labToVal_extension_comp, INIT_MEM_def_on_cache.
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
                                labToVal l z m /\
                                I m tl
              | _ => False
            end).
Proof.
  intros v l Heval_var I.
  destruct initial_m0.
  inv Hhandler.
  assert (Hmem0: mem_def_on_cache cblock m0) by (eapply INIT_MEM_def_on_cache; eauto).
  case_eq v; intros; eapply HT_strengthen_premise;
  try eapply loadFromCache_spec; eauto; intros; intuition;
  eexists; split; eauto using extension_comp_value_on_cache;
  split; eauto;
  split; eauto; simpl;
  subst; unfold nth_labToVal in *; eauto using labToVal_extension_comp.
  - destruct (le_lt_dec n 0); try omega.
    erewrite nth_order_proof_irrel; eauto using labToVal_extension_comp.
  - destruct (le_lt_dec n 1); try omega.
    erewrite nth_order_proof_irrel; eauto using labToVal_extension_comp.
  - destruct (le_lt_dec n 2); try omega.
    erewrite nth_order_proof_irrel; eauto using labToVal_extension_comp.
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
                         | (z, t) ::: tl => I m tl /\ labToVal l z m  /\
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
    + eapply HT_strengthen_premise.
      eapply (IHe1 (eval_expr eval_var e1) (eq_refl _)
                   (fun m s =>
                      match s with
                        | (z,t):::tl => I m tl
                                             /\ labToVal (eval_expr eval_var e2) z m
                                             /\ extends m0 m /\ INIT_MEM m
                        | _ => False
                      end)); eauto.
      unfold extension_comp, extends.
      destruct s; intuition.
      destruct c; intuition.
      destruct a.
      destruct v; intuition eauto using labToVal_extension_comp.
      go_match.
    + eapply HT_strengthen_premise.
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
                           | (Vint z,t):::tl => I m tl /\ boolToZ b = z /\
                                                extends m0 m /\ INIT_MEM m
                           | _ => False
                       end).
Proof.
  induction c; intros; simpl;
    try (simpl in H); subst.

  (* True *)
  eapply HT_strengthen_premise.
  eapply push_spec. go_match. intuition eauto.

  (* False *)
  eapply HT_strengthen_premise.
  eapply push_spec. go_match. intuition eauto.

  (* Flows *)
  eapply HT_compose.
  eapply genExpr_spec; eauto.

  eapply HT_compose.
  eapply HT_strengthen_premise; eauto.
  eapply (genExpr_spec r (eval_expr eval_var r) (eq_refl _))
  with
  (I:= fun m s =>
         match s with
           | (z, t) ::: tl => I m tl /\ labToVal (eval_expr eval_var r0) z m /\
                                   extends m0 m
           | _ => False
     end).
    unfold extension_comp, extends; simpl.
    intros.
    destruct s; intuition.
    destruct c; intuition.
    destruct a.
    destruct v; intuition eauto using labToVal_extension_comp.
    go_match.
  eapply HT_consequence.
  eapply (genFlows_spec' cblock table (eval_expr eval_var r) (eval_expr eval_var r0)
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
                      | (Vint z,t):::tl => I m tl
                        /\ boolToZ (eval_cond eval_var c2) = z
                        /\ extends m0 m
                      | _ => False
                    end)); eauto.
  unfold extension_comp, extends; simpl.
  intuition; eauto. go_match.

  go_match.

  eapply HT_consequence.
  eapply (genAnd_spec_I) with (I:= fun m s => extends m0 m /\ I m s) ; eauto.
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
                      | (Vint z,t):::tl => I m tl
                        /\ boolToZ (eval_cond eval_var c2) = z
                        /\ extends m0 m
                      | _ => False
                    end)); eauto.
  unfold extension_comp, extends; simpl.
  intuition; eauto. go_match.
  go_match.

  eapply HT_consequence.
  eapply (genOr_spec_I) with (I:= fun m s => extends m0 m /\ I m s) ; eauto.
  go_match.
  go_match.
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

(* XXX: could factor out all the [apply_rule] assumptions
   below as:

     Parameter ar.
     Hypothesis apply_rule_eq: apply_rule am vls pcl = ar.

   and then use [ar] in place of [apply_rule am vls pcl] everywhere.
*)

Lemma genApplyRule_spec_Some:
  forall l1 l2,
    apply_rule am pcl vls = Some (l1, l2) ->
    forall I (Hext: extension_comp I),
      HT   (genApplyRule am)
           (fun m s => extends m0 m /\ I m s)
           (fun m s => match s with
                           | (Vint some1, t1) ::: (zr, t3) ::: (zrpc, t4) ::: tl =>
                             1 = some1 (* [Some (...)] *)
                             /\ labToVal l1 zrpc m /\ labToVal l2 zr m
                             /\ extends m0 m /\ I m tl
                           | _ => False
                       end).
Proof.
  introv Happly.
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.
  inv  Happly. intros I Hext.

  - eapply (ite_spec_specialized_I' cblock table (boolToZ true)); eauto.

    + eapply HT_weaken_conclusion.
      eapply (genScond_spec (allow am) true H I); eauto.
      go_match.

    + intros.
      eapply HT_strengthen_premise.
      eapply some_spec'.

      eapply HT_compose.
      eapply genExpr_spec with (I:= I); eauto.

      eapply HT_consequence.
      eapply genExpr_spec with
      (I:= fun m s => match s with
                        | (z, t) ::: tl0 =>
                          I m tl0
                          /\ labToVal (eval_expr eval_var (labResPC am)) z m
                          /\ extends m0 m
                        | _ => False
                      end); eauto.
      * unfold extension_comp, extends in *.
        simpl. intuition. go_match. eauto using labToVal_extension_comp.
      * unfold extension_comp, extends in *.
        simpl. intuition. go_match. eauto using labToVal_extension_comp.
        go_match.
      * go_match.
      * eauto.
    + intros; false; omega.
Qed.

Lemma genApplyRule_spec_None:
    apply_rule am pcl vls  = None ->
    forall I (Hext: extension_comp I),
      HT   (genApplyRule am)
           (fun m s => extends m0 m /\ I m s)
           (fun m s => match s with
                         | (Vint none1, t1) :::  tl =>
                           0 = none1  (* [None] *)
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

  eapply HT_strengthen_premise.
  eapply (push_spec cblock table 0); eauto.
  go_match.
  intuition auto.
Qed.

Definition listify_apply_rule (ar: option (T * T))
                              (s0: stack) (zr zpc: val privilege) : stack -> Prop :=
  match ar with
  | None           => fun s => exists t, s = CData (Vint 0, t) :: s0
  | Some (lpc, lr) => fun s => exists t1 t2 t3, s = CData (Vint 1, t1)   ::
                                                    CData (zr, t2)  ::
                                                    CData (zpc, t3) :: s0
  end.

Definition labToVal_rule_res (ar: option (T * T)) (zr zpc: val privilege) m : Prop :=
  match ar with
  | None           => True
  | Some (lpc, lr) => labToVal lr zr m /\ labToVal lpc zpc m
  end.

Lemma genApplyRule_spec:
  forall ar,
    apply_rule am pcl vls = ar ->
    forall I (Hext: extension_comp I),
      HT   (genApplyRule am)
           (fun m s => extends m0 m /\ I m s)
           (fun m s => extends m0 m /\
                       exists s0 zr zrpc,
                       labToVal_rule_res ar zr zrpc m /\
                       listify_apply_rule ar s0 zr zrpc s /\
                       I m s0).
Proof.
  intros.
  unfold listify_apply_rule, labToVal_rule_res.
  case_eq ar ; [intros [r rpc] | intros rpc] ; intros ; subst.
  - eapply HT_weaken_conclusion.
    eapply (genApplyRule_spec_Some r rpc H0 I); eauto.
    go_match.
    do 5 eexists; eauto.
  - eapply HT_weaken_conclusion.
    eapply genApplyRule_spec_None; eauto.
    go_match. eexists. eexists (Vint 0). eexists (Vint 0).
    eauto.
Qed.

Lemma genApplyRule_spec_GT_ext:
  forall ar,
    apply_rule am pcl vls = ar ->
    forall (I:HProp) (Hext: extension_comp I),
      GT_ext cblock table (genApplyRule am)
         (fun m s => extends m0 m /\ I m s)
         (fun m0' s0 m s => extends m0 m0' /\ extends m0' m /\
                            exists zr zrpc,
                              labToVal_rule_res ar zr zrpc m /\
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
                       | (Vint z,t):::tl =>
                         extends m0 m /\
                         boolToZ (opCodeToZ opcode' =? opCodeToZ opcode) = z /\
                         I m tl
                       | _ => False
                   end).
Proof.
  destruct initial_m0.
  inv Hhandler. intuition.
  unfold genCheckOp.
  eapply HT_weaken_conclusion.
  eapply genTestEqual_spec_I; try assumption. intros I' HextI'.
  eapply HT_strengthen_premise.
  eapply push_spec.
  go_match. intuition eauto.
  intros I' HextI'.
  eapply HT_strengthen_premise.
  eapply loadFromCache_spec; eauto.
  go_match.
  eexists. split; eauto. intuition eauto using extension_comp_value_on_cache.
  go_match. intuition.
  go_match.
  simpl.
  intuition.
  destruct (EquivDec.equiv_dec (Vint (opCodeToZ opcode))
                               (Vint (opCodeToZ opcode'))) as [E|E]; simpl in E.
  - inv E.
    rewrite Z.eqb_refl. reflexivity.
  - assert (NEQ : opCodeToZ opcode' <> opCodeToZ opcode) by congruence.
    rewrite <- Z.eqb_neq in NEQ.
    rewrite NEQ. reflexivity.
Qed.

Lemma genCheckOp_spec_GT_ext:
  forall opcode' I (Hext: extension_comp I),
    GT_ext cblock table (genCheckOp opcode')
       (fun m s => extends m0 m /\ I m s)
       (fun m0' s0 m s => exists t, extends m0 m0' /\ extends m0' m /\
                          s = (Vint (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode))
                               ,t) ::: s0
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

Variable (opcode: OpCode).
Let n := labelCount opcode.
Let am := fetch_rule opcode.

Variable (vls: Vector.t T n).
Variable (pcl: T).

Let eval_var := mk_eval_var vls pcl.

Hypothesis H_apply_rule: apply_rule am pcl vls = ar.

(* Don't really need to specify [Qnil] since it will never run *)
Definition Qnil: GProp := fun m0' s0 m s => True.
Definition genV: OpCode -> HFun :=
  fun i _ _ => boolToZ (opCodeToZ i =? opCodeToZ opcode).
Definition genC: OpCode -> code := genCheckOp.
Definition genB: OpCode -> code := genApplyRule'.
Definition genQ: HProp -> OpCode -> GProp :=
         (fun I i m0' s0 m s => extends m0' m /\
                                exists zr zrpc,
                                  labToVal_rule_res ar zr zrpc m /\
                                  listify_apply_rule ar s0 zr zrpc s /\ I m s0).

Let INIT_MEM := INIT_MEM opcode vls pcl.

Variable m0 : memory.
Hypothesis INIT_MEM0: INIT_MEM m0.

Lemma genCheckOp_spec_GT_push_v_ext:
  forall opcode' I (Hext: extension_comp I),
    GT_push_v_ext cblock table (genC opcode')
                  (fun m s => extends m0 m /\ I m s)
                  (genV opcode').
Proof.
  intros; eapply GT_consequence'_ext; eauto.
  eapply genCheckOp_spec_GT_ext with (I:= fun m s => extends m0 m /\ I m s); eauto.
  unfold extension_comp, extends in *; intuition ; eauto.
  intuition.
  simpl.
  split_vc.
Qed.

Lemma dec_eq_OpCode: forall (o o': OpCode),
  o = o' \/ o <> o'.
Proof.
  destruct o; destruct o'; solve [ left; reflexivity | right; congruence ].
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
    GT_guard_v_ext cblock table (genB opcode')
               (fun m s => extends m0 m /\ I m s)
               (genV opcode')
               (genQ I opcode').
Proof.
  intros.
  cases (dec_eq_OpCode opcode' opcode) as Eq; clear Eq. substs.
  - eapply GT_consequence'_ext; try assumption.
    unfold genB, genApplyRule'.
    eapply genApplyRule_spec_GT_ext; eauto.
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
                        indexed_hyps_ext cblock table _ genC genB (genQ I)
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

Variable (opcode: OpCode).
Let n := labelCount opcode.
Let am := fetch_rule opcode.

Variable (vls: Vector.t T n).
Variable (pcl: T).

Let eval_var := mk_eval_var vls pcl.

Hypothesis H_apply_rule: apply_rule am pcl vls = ar.
Let INIT_MEM := INIT_MEM opcode vls pcl.

Lemma genComputeResults_spec_GT_ext: forall I (Hext: extension_comp I)
                                       m0 (INIT_MEM0: INIT_MEM m0),
    GT_ext cblock table genComputeResults
       (fun m s => extends m0 m /\ I m s)
       (fun m0' s0 m s => extends m0 m0' /\ extends m0' m /\
                          exists zr zpc,
                            labToVal_rule_res ar zr zpc m /\
                            listify_apply_rule ar s0 zr zpc s /\ I m s0).
Proof.
  intros.
  unfold genComputeResults.
  eapply GT_consequence'_ext; try assumption.
  eapply indexed_cases_spec_ext with
  (Qnil:= Qnil)
  (genV:= genV opcode)
  (P:= fun m s => extends m0 m /\ I m s)
  (genQ:= genQ ar I); try assumption.
  - Case "default case that we never reach".
    unfold GT_ext; intros.
    eapply HT_strengthen_premise.
    eapply nop_spec.
    intros. intuition; subst.
    unfold extends in * ; eauto.
    eauto.
    unfold Qnil; iauto.
  - eapply (H_indexed_hyps ar opcode vls pcl H_apply_rule m0 INIT_MEM0  I); auto.
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
      HT   genComputeResults
           (fun m s => extends m0 m /\ s = s0 /\ I m0 s /\ I m s)
           (fun m s => extends m0 m /\
                       exists zr zpc,
                         labToVal_rule_res ar zr zpc m /\
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
                               store cblock a vl m0 = Some m /\
                               Q m s)
     Q.
Proof.
  intros.
  eapply HT_compose_flip.
  eapply store_spec_wp'; eauto.
  unfold push.
  eapply HT_strengthen_premise.
  eapply push_cptr_spec.

  intuition; eauto. destruct H as [vl [s0 [m0 Hint]]]. intuition; substs.
  do 5 eexists; intuition; eauto.
Qed.

Lemma genStoreResults_spec_Some: forall Q,
  forall lr lpc,
    ar = Some (lpc,lr) ->
      HT genStoreResults
         (fun m s => exists s0 zr zpc,
            labToVal_rule_res ar zr zpc m /\
            listify_apply_rule ar s0 zr zpc s /\
            valid_address cblock addrTagRes m /\
            valid_address cblock addrTagResPC m /\
            forall t1 t2,
            exists m' m'',
              (store cblock addrTagRes (zr,t1) m = Some m')
               /\ store cblock addrTagResPC (zpc,t2) m' = Some m''
               /\ labToVal_rule_res ar zr zpc m''
               /\ Q m'' ((Vint 1,handlerTag):::s0))
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
  split_vc.
  edestruct H4 as [m' [m'' Hint]]. intuition.
  subst.

  split_vc.
  inv H7.
Qed.

Lemma genStoreResults_spec_None: forall Q: memory -> stack -> Prop,
  ar = None ->
    HT genStoreResults
       (fun m s => exists s0 zr zpc,
                     labToVal_rule_res ar zr zpc m /\
                     listify_apply_rule ar s0 zr zpc s /\
                     (forall m0,
                       extends m m0 -> Q m0 ((Vint 0,handlerTag) ::: s0)))
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

  intros. destruct H as [s0 [zr [zpc [t Hint]]]].
  split_vc.
  eauto using extends_refl.
Qed.

Lemma faultHandler_specEscape_Some: forall raddr lr lpc m0,
  INIT_MEM m0 ->
  valid_address cblock addrTagRes m0 ->
  valid_address cblock addrTagResPC m0 ->
  ar = Some (lpc, lr) ->
  forall s0,
    HTEscape cblock table raddr faultHandler
             (fun m s => m = m0 /\
                         s = (CRet raddr false false::s0))
             (fun m s => ( exists zr zpc,
                             s = s0 /\
                             handler_final_mem_matches lpc lr m0 m zpc zr
                         , Success )).
Proof.
  intros.
  unfold faultHandler.

  eapply HTEscape_compose_flip.
  eapply HTEscape_compose_flip.

  eapply genSysRet_specEscape_Some ; eauto.
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
              store cblock addrTagRes (zr, t1) m = Some m' /\
              store cblock addrTagResPC (zpc, t2) m' = Some m'').
  {
   exploit (extends_valid_address cblock m0 m addrTagRes); eauto. intros HvalidRes.
   exploit (extends_valid_address cblock m0 m addrTagResPC); eauto. intros HvalidResPC.
   eapply (valid_store _ _ _ cblock addrTagRes (zr,t1)) in HvalidRes.
   destruct HvalidRes as [m' ?].
   eapply valid_address_upd with (a:= addrTagResPC) in HvalidResPC; eauto.
   eapply valid_store in HvalidResPC.
   destruct HvalidResPC as [m'' ?]; eauto.
  }

  destruct Hm'm'' as [m' [m'' [Hm' Hm'']]].
  assert (Hup: mem_eq_except_cache cblock m m''); eauto.
  {
    econstructor.
    - eapply INIT_MEM_def_on_cache; eauto using extension_comp_INIT_MEM.
    - intros b.
      unfold store in *.
      intros fr KERNEL NEQ DEF.
      rewrite <- DEF.
      transitivity (Mem.get_frame m' b);
      eapply get_frame_store_neq; eauto;
      assumption.
  }
  do 2 eexists ; intuition; eauto.
  {  unfold labToVal_rule_res in *.
     rewrite H2 in *. intuition; eapply labToVal_cache; eauto.
  }
  eexists; intuition; eauto.
  exists zr ; exists zpc ; intuition; eauto.
  exists m. intuition; eauto.
  {  unfold labToVal_rule_res in *.
     rewrite H2 in *. intuition; eapply labToVal_cache; eauto.
  }
  {  unfold labToVal_rule_res in *.
     rewrite H2 in *. intuition; eapply labToVal_cache; eauto.
  }
  { assert (Hm''' : load cblock addrTagRes m'' = Some (zr, t1)).
    { eapply load_store_new in Hm'.
      erewrite load_store_old; eauto.
      compute; congruence. }
    clear Hm'.
    eapply load_store_new in Hm''.
    unfold load, cache_hit_read_mem in *.
    destruct (Mem.get_frame m'' cblock) as [fr|]; try congruence.
    econstructor; econstructor; eauto.
  }

  unfold update_cache_spec_rvec. destruct Hup.
  clear - Hm' Hm'' stamp_cblock.
  split.
  - split.
    + intros b fr USER DEF.
      rewrite <- DEF.
      transitivity (Mem.get_frame m' b);
      eapply get_frame_store_neq; eauto; congruence.
    + intros b fr _ NEQ DEF.
      rewrite <- DEF.
      transitivity (Mem.get_frame m' b);
      eapply get_frame_store_neq; eauto.
  - intros addr NEQ1 NEQ2.
    symmetry.
    transitivity (load cblock addr m');
    eapply load_store_old; eauto; congruence.
Qed.

Lemma faultHandler_specEscape_None: forall raddr m0,
                                    forall (INIT_MEM0: INIT_MEM m0),
  ar = None ->
  forall s0,
    HTEscape cblock table raddr faultHandler
             (fun m s => m0  = m /\ s = s0)
             (fun m s => ((extends m0 m /\ s = s0)
                         , Failure)).
Proof.
  intros.
  unfold faultHandler.
  eapply HTEscape_compose_flip.
  eapply HTEscape_compose_flip.
  eapply genSysRet_specEscape_None ; eauto.
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

Variable cblock : block.
Variable stamp_cblock : Mem.stamp cblock = Kernel.
Variable table : CSysTable.

Context {T : Type}
        {Latt : JoinSemiLattice T}
        {CLatt : ConcreteLattice T}
        {WFCLatt : WfConcreteLattice cblock table T Latt CLatt}.

Variable labelCount : OpCode -> nat.
Variable fetch_rule : forall (opcode:OpCode), AllowModify (labelCount opcode).
Definition handler : list Instr := faultHandler _ fetch_rule.

Require Import ConcreteExecutions.

Theorem handler_correct_succeed : handler_spec_succeed cblock table labelCount fetch_rule handler.
Proof.
 unfold handler_spec_succeed.
 intros.
  assert (valid_address cblock addrTagRes c).
  { unfold cache_hit_mem, valid_address, load in *.
    destruct (Mem.get_frame c cblock) as [fr|]; try solve [intuition].
    inv INPUT. inv TAGR. eauto. }
  assert (valid_address cblock addrTagResPC c).
  { unfold cache_hit_mem, valid_address, load in *.
    destruct (Mem.get_frame c cblock) as [fr|]; try solve [intuition].
    inv INPUT. inv TAGRPC. eauto. }
  edestruct (faultHandler_specEscape_Some cblock stamp_cblock table
                                          _ fetch_rule
                                          (Some (lpc,lr))
                                          opcode vls pcl RULE raddr lr lpc c)
    as [stk1 HH]; eauto.
 - exploit (@init_enough cblock stamp_cblock table _ fetch_rule _ _ _ _ (labelCount opcode) vls); eauto.
   intros Hmem.
   repeat match goal with
            | H : valid_address _ _ _ |- _ =>
              destruct H as ([? ?] & ?)
          end;
   econstructor; simpl in LABS; intuition; eauto;
   econstructor; eauto.
 - destruct HH as [cache1 [pc1 [priv1 [[zr [zpc' [P1 P2]]] [P3 P4]]]]].
   subst. inv P3.
   exists cache1;  exists zr; exists zpc'.
   split; auto.
   eapply P4.
Qed.

Theorem handler_correct_fail : handler_spec_fail cblock table labelCount fetch_rule handler.
Proof.
  unfold handler_spec_fail.
  intros.
  assert (valid_address cblock addrTagRes c).
  { unfold cache_hit_mem, valid_address, load in *.
    destruct (Mem.get_frame c cblock) as [fr|]; try solve [intuition].
    inv INPUT. inv TAGR. eauto. }
  assert (valid_address cblock addrTagResPC c).
  { unfold cache_hit_mem, valid_address, load in *.
    destruct (Mem.get_frame c cblock) as [fr|]; try solve [intuition].
    inv INPUT. inv TAGRPC. eauto. }
  edestruct (faultHandler_specEscape_None cblock stamp_cblock table _ fetch_rule None opcode vls pcl RULE raddr c)
      as [stk1 HH]; eauto.
  - exploit (@init_enough cblock stamp_cblock table _ fetch_rule _ _ _ _ (labelCount opcode)); eauto.
    intros Hmem.
    repeat match goal with
             | H : valid_address _ _ _ |- _ =>
               destruct H as ([? ?] & ?)
           end;
    econstructor; simpl in LABS; intuition; eauto;
    econstructor; eauto.
  - destruct HH as [cache1 [pc1 [priv1 [[P1 P2] [P3 P4]]]]].
    substs. inv P3.
    eexists ; eexists; intuition; eauto.
Qed.

End HandlerCorrect.
