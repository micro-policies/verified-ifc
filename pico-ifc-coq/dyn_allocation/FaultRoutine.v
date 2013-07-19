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
Require Import CodeSpecs. 
Require Import CodeGen.
Require Import CLattices.
Require Import ConcreteExecutions.

Notation Atom := (Atom Z privilege).
Notation memory := (Mem.t Atom privilege).
Notation PcAtom := (PcAtom Z).
Notation block := (block privilege).

Section TMU. 

Open Local Scope Z_scope.

Variable cblock : block.
Variable stamp_cblock : Mem.stamp cblock = Kernel.

Notation cget := (cget cblock).
Notation cache_hit_mem := (cache_hit_mem cblock).
Notation HT := (HT cblock).
Notation GT := (GT cblock).

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}
        {WFCLatt: WfConcreteLattice cblock T Latt CLatt}. 


(* --------------------- TMU Fault Handler code ----------------------------------- *)

(* Compilation of rules *)

Definition genError :=
  push (-1) ++ [Jump].

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

Section FaultHandler.

Definition genCheckOp (op:OpCode): code :=
  genTestEqual (push (opCodeToZ op)) (loadFromCache addrOpLabel).

Definition fetch_rule_impl_type: Type := forall (opcode:OpCode),  {n:nat & AllowModify n}.

Variable fetch_rule_impl: fetch_rule_impl_type.

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

(* NC: or

   ite (genComputeResults ++ genStoreResults)
        [Ret]
        genError.
*)

End FaultHandler.


(* ================================================================ *)
(* Fault-handler Code Specifications                                *)

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

(* NC: this took a few tries ... *)
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

Section TMUSpecs.

Definition handlerLabel := bot. 

Definition handler_initial_mem_matches 
           (opcode: Z)
           (tag1: Z) (tag2: Z) (tag3: Z) (pctag: Z) 
           (m: memory) : Prop := 
  exists cache,
    cget m = Some cache /\
     (exists tag, index_list_Z addrOpLabel cache = Some (Vint opcode,tag))
  /\ (exists tag, index_list_Z addrTag1 cache = Some (Vint tag1,tag))
  /\ (exists tag, index_list_Z addrTag2 cache = Some (Vint tag2,tag))
  /\ (exists tag, index_list_Z addrTag3 cache = Some (Vint tag3,tag))
  /\ (exists tag, index_list_Z addrTagPC cache = Some (Vint pctag,tag))
.


(* APT: Just a little sanity check that these definitions are somewhat coherent. *)
Lemma init_init: forall (m:memory)  op ts tpc, cache_hit_mem m op ts tpc ->
let '(l1,l2,l3) := ts in
handler_initial_mem_matches op l1 l2 l3 tpc m.
Proof.
  unfold Concrete.cache_hit_mem.
  intros.
  destruct (Mem.get_frame m cblock) eqn:E; try (elim H; fail).  
  inv H. inv OP. inv TAG1. inv TAG2. inv TAG3. inv TAGPC. 
  econstructor; jauto.
Qed.


(* Connecting to the definition used in ConcreteMachine.v *)
Lemma init_enough: forall {n} (vls:Vector.t T n) m opcode pcl,
    cache_hit_mem m (opCodeToZ opcode) (labsToZs vls) (labToZ pcl) ->
    handler_initial_mem_matches 
      (opCodeToZ opcode) 
      (nth_labToZ vls 0)  
      (nth_labToZ vls 1)
      (nth_labToZ vls 2)
      (labToZ pcl)
      m.
Proof.
  intros. unfold labsToZs in H. 
  unfold Concrete.cache_hit_mem in *.
  destruct (Mem.get_frame m cblock) eqn:E; try (intuition; fail).
  inv H. inv UNPACK. inv OP. inv TAG1. inv TAG2. inv TAG3. inv TAGPC. 
  econstructor; jauto.
Qed.

Variable fetch_rule_impl: fetch_rule_impl_type.
Variable (opcode: OpCode).
Definition n := projT1 (fetch_rule_impl opcode).
Definition am := projT2 (fetch_rule_impl opcode).
Variable (vls: Vector.t T n).
Variable (pcl: T).
Variable (m0: memory).

Hypothesis initial_mem_matches:
  handler_initial_mem_matches
    (opCodeToZ opcode)
    (nth_labToZ vls 0)
    (nth_labToZ vls 1)
    (nth_labToZ vls 2)
    (labToZ pcl) m0.

Definition eval_var := mk_eval_var vls pcl.

Ltac clean_up_initial_mem :=
  unfold handler_initial_mem_matches in *;
  intuition;
  generalize initial_mem_matches; intros HH; clear initial_mem_matches;
  jauto_set_hyps; intros.

Lemma genVar_spec:
  forall v l,
    eval_var v = l ->
    forall s0,
      HT  (genVar v)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (Vint (labToZ l), handlerTag) :: s0).
Proof.
  intros v l Heval_var s0.

  clean_up_initial_mem.

  destruct v; simpl; eapply loadFromCache_spec;
  simpl in *; unfold load; auto;
  unfold ConcreteMachine.cget in *; rewrite H.

  (* Most of the cases are very similar ... *)
  Ltac nth_order_case k :=
    erewrite (nth_order_valid n vls k) in *;
    intuition;
    subst; auto;
    eauto.

  nth_order_case 0%nat.
  nth_order_case 1%nat.
  nth_order_case 2%nat.

  subst; eauto.
Qed.

Lemma genExpr_spec: forall (e: rule_expr n),
  forall l,
    eval_expr eval_var e = l ->
    forall s0,
      HT  (genExpr e)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (Vint (labToZ l), handlerTag) :: s0).
Proof.
  induction e; intros ? Heval_expr ?;
    simpl; simpl in Heval_expr.
  subst l. 
  eapply genBot_spec; eauto. 
  eapply genVar_spec; eauto.
  eapply HT_compose.
  eapply IHe2; eauto.
  eapply HT_compose.
  eapply IHe1; eauto.
  rewrite <- Heval_expr.
  eapply genJoin_spec.
  auto.
Qed.


Lemma genCond_spec: forall (c: rule_cond n),
  forall b,
    eval_cond eval_var c = b ->
    forall s0,
      HT (genCond c)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (Vint (boolToZ b), handlerTag) :: s0).
Proof.
  induction c; intros; simpl;
    try (simpl in H); subst.

  (* True *)
  eapply push_spec''.

  (* Flows *)
  eapply HT_compose.
  eapply genExpr_spec.
  eauto.
  eapply HT_compose.
  eapply genExpr_spec.
  eauto.
  eapply genFlows_spec.
  auto.

  (* And *)
  eapply HT_compose.
  eapply IHc2.
  eauto.
  eapply HT_compose.
  eapply IHc1.
  eauto.
  eapply genAnd_spec; auto.

  (* Or *)
  eapply HT_compose.
  eapply IHc2.
  eauto.
  eapply HT_compose.
  eapply IHc1.
  eauto.
  eapply genOr_spec; auto.
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
  forall lrpc lr,
    apply_rule am pcl vls = Some (lrpc, lr) ->
    forall s0,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (   Vint 1, handlerTag) :: (* [Some (...)] *)
                           CData (Vint (labToZ lr), handlerTag) ::
                           CData (Vint (labToZ lrpc), handlerTag) :: s0).
Proof.
  introv Happly. intros.
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.
  inversion Happly; subst.

  eapply ite_spec_specialized with (v:=boolToZ true); auto.
    eapply genCond_spec; auto.

    intros.

    eapply some_spec.
    eapply HT_compose.
      apply genExpr_spec.
      eauto.

      eapply genExpr_spec.
      eauto.

    intros; false; omega.
Qed.

Lemma genApplyRule_spec_None:
    apply_rule am pcl vls = None ->
    forall s0,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (Vint 0, handlerTag) :: s0). (* [None] *)
Proof.
  introv Happly. intros.
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.

  eapply ite_spec_specialized with (v:=boolToZ false); auto; intros.
    eapply genCond_spec; auto.

    unfold boolToZ in *; false; omega.

    apply none_spec.
Qed.

Definition listify_apply_rule
  (ar: option (T * T)) (s0: stack): stack
:=
  match ar with
  | None            => CData (Vint 0, handlerTag) :: s0
  | Some (lrpc, lr) => CData (Vint 1, handlerTag) ::
                        CData (Vint (labToZ lr), handlerTag) ::
                        CData (Vint (labToZ lrpc), handlerTag) :: s0
  end.

Lemma genApplyRule_spec:
  forall ar,
    apply_rule am pcl vls = ar ->
    forall s0,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = listify_apply_rule ar s0).
Proof.
  intros.
  case_eq ar; intros p ?; subst.
  - destruct p as [lrpc lr].
    eapply genApplyRule_spec_Some; eauto.
  - eapply genApplyRule_spec_None; eauto.
Qed.

Lemma genApplyRule_spec_GT:
  forall ar,
    apply_rule am pcl vls = ar ->
      GT (genApplyRule am)
         (fun m s => m = m0)
         (fun m0' s0 m s => m = m0 /\
                            s = listify_apply_rule ar s0).
Proof.
  unfold CodeSpecs.GT; intros.
  eapply HT_consequence; eauto.
  - eapply genApplyRule_spec; eauto.
  - simpl; intuition (subst; eauto).
  - simpl; intuition (subst; eauto).
Qed.

Lemma genCheckOp_spec:
  forall opcode', forall s0,
    HT (genCheckOp opcode')
      (fun m s => m = m0 /\
                  s = s0)
      (fun m s => m = m0 /\
                  s = (Vint (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode))
                      ,handlerTag) ::: s0).
Proof.
  clean_up_initial_mem.
  intros.
  unfold genCheckOp.
  eapply genTestEqual_spec; auto.
  eapply push_spec''.
  intros.
  eapply loadFromCache_spec; auto.
  unfold load; unfold ConcreteMachine.cget in *; rewrite H.
  eauto.
Qed.

Lemma genCheckOp_spec_GT:
  forall opcode',
    GT (genCheckOp opcode')
       (fun m s => m = m0)
       (fun m0' s0 m s => m = m0 /\
                          s = (Vint (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode))
                               ,handlerTag) ::: s0).
Proof.
  unfold CodeSpecs.GT; intros.
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
    GT_push_v cblock (genC opcode')
              (fun m s => m = m0)
              (genV opcode').
Proof.
  intros; eapply GT_consequence'; auto.
  eapply genCheckOp_spec_GT.
  eauto.
  intuition (subst; intuition).
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

Lemma genApplyRule'_spec_GT_guard_v:
  forall opcode',
    GT_guard_v cblock
               (genB opcode')
               (fun m s => m = m0)
               (genV opcode')
               (genQ opcode').
Proof.
  (* NC: This proof is ugly ... not sure where I've gone wrong, but I
  have ... *)
  intros.
  cases (dec_eq_OpCode opcode' opcode) as Eq; clear Eq.
  - eapply GT_consequence'; auto.
    + unfold genB, genApplyRule'.
      subst opcode'.
      fold am.
      eapply genApplyRule_spec_GT; eauto.
    + iauto.
    + (* why does iauto no longer work here?? *)
      subst ar. intros.  subst m1. econstructor. intuition. subst ar. intuition.
  - unfold GT_guard_v, CodeSpecs.GT, CodeSpecs.HT.
    intros.
    unfold genV in *.
    pose (opCodeToZ_inj opcode opcode').
    false; intuition. 
Qed. 

Lemma H_indexed_hyps: indexed_hyps cblock _ genC genB genQ genV (fun m s => m = m0) opcodes.
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
  eapply GT_consequence'; auto.
  unfold genComputeResults.
  eapply indexed_cases_spec with (Qnil:=Qnil); auto.
  - Case "default case that we never reach".
    unfold CodeSpecs.GT; intros.
    eapply HT_consequence.
    eapply nop_spec.
    iauto.
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
    destruct opcode; simpl; intuition.
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
  valid_address cblock addrTagRes m0 ->
  valid_address cblock addrTagResPC m0 ->
  ar = Some (lrpc, lr) ->
  forall s0,
    HT genStoreResults
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s =>
        (exists m', store cblock addrTagRes (Vint (labToZ lr),handlerTag) m0
                    = Some m'
                 /\ store cblock addrTagResPC (Vint (labToZ lrpc),handlerTag) m'
                    = Some m)
        /\ s = (Vint 1,handlerTag) ::: s0).
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
  eapply storeAt_spec_wp; auto.
  eapply storeAt_spec_wp; auto.

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
                   s = (Vint 0,handlerTag) ::: s0).
Proof.
  introv Har_eq; intros.
  unfold listify_apply_rule.
  rewrite Har_eq.
  unfold genStoreResults.

  eapply HT_strengthen_premise.
  eapply ifNZ_spec_Z with (v:=0).
  eapply genFalse_spec.

  reflexivity.
  jauto.
Qed.

(* The irrelevant memory never changes *)
Lemma genStoreResults_update_cache_spec_rvec:
  valid_address cblock addrTagRes m0 ->
  valid_address cblock addrTagResPC m0 ->
  forall s0,
    HT genStoreResults
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => update_cache_spec_rvec cblock m0 m).
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
    split.
    * intros args NEQ.
      symmetry.
      exploit get_frame_store_neq; eauto.
      intros E. rewrite E. clear E H2.
      exploit get_frame_store_neq; eauto.
    * intros.
      rewrite (load_store_old H2); try congruence.
      rewrite (load_store_old H1); congruence.

  + eapply HT_weaken_conclusion;
    rewrite <- Eq_ar in *.

    eapply genStoreResults_spec_None; eauto.

    simpl; intuition; subst; auto.
    intros addr NEQ. trivial.
Qed.

Definition handler_final_mem_matches (lrpc: T) (lr: T) (m: memory) (m': memory) :Prop :=
     cache_hit_read_mem cblock m' (labToZ lr) (labToZ lrpc) 
  (* Nothing else changed *)
  /\ update_cache_spec_rvec cblock m m'.

Lemma genStoreResults_spec_Some': forall lr lpc,
  valid_address cblock addrTagRes m0 ->
  valid_address cblock addrTagResPC m0 ->
  ar = Some (lpc, lr) ->
  forall s0,
    HT genStoreResults
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => handler_final_mem_matches lpc lr m0 m
                   /\ s = (Vint 1,handlerTag) ::: s0).
Proof.
  introv HvalidRes HvalidResPC Har_eq; intros.
  destruct HvalidRes as [m' Hm'].
  destruct HvalidResPC as [m'' Hm''].
  destruct (load_some_store_some Hm' (Vint (labToZ lr), handlerTag)) as [m''' T'].
  assert (TT:exists m'''', 
            store cblock addrTagResPC (Vint (labToZ lpc), handlerTag) m''' = Some m'''').
    eapply load_some_store_some.
    erewrite load_store_old; eauto.
    compute; congruence.
  destruct TT as [m4 T4].
  unfold genStoreResults.
  eapply HT_strengthen_premise.
  eapply ifNZ_spec_NZ with (v := 1); try omega.
  eapply HT_compose_flip.
  eapply HT_compose_flip.
  eapply genTrue_spec_wp.
  simpl.
  eapply storeAt_spec_wp; auto.
  eapply storeAt_spec_wp; auto.
  rewrite Har_eq. simpl.
  intros m s [Hm Hs]. subst.
  eexists.
  repeat (split; eauto); try econstructor; eauto.
  + unfold cache_hit_read_mem.
    generalize (load_store_new T4).
    exploit (load_store_old T4 cblock addrTagRes).
    compute; congruence.
    intros EE.
    generalize (load_store_new T').
    rewrite <- EE.
    unfold load.
    destruct (Mem.get_frame m4 cblock) eqn:E; try congruence.
    econstructor;
    constructor; auto.
  + intros addr NEQ.
    exploit get_frame_store_neq; eauto.
    intros E. rewrite E. clear T4.
    exploit get_frame_store_neq; eauto.
  + intros ofs H1 H2.
    exploit (load_store_old T4 cblock ofs); try congruence.
    exploit (load_store_old T' cblock ofs); try congruence.
Qed.

Lemma genError_specEscape: forall raddr (P: memory -> stack -> Prop),
  HTEscape cblock raddr genError
           P
           (fun m s => (P m s , Failure)).
Proof.
  intros.
  unfold genError.
  eapply HTEscape_compose.
  - eapply push_spec'.
  - eapply HTEscape_strengthen_premise.
    + eapply jump_specEscape_Failure; auto.
    + intuition.
      cases s; subst.
      * rewrite hd_error_nil in *; false.
      * rewrite hd_error_cons in *.
        inversion H0; subst; jauto.
Qed.

Definition genFaultHandlerReturn: code := ifNZ [Ret] genError.

Lemma genFaultHandlerReturn_specEscape_Some: forall raddr lr lpc,
  forall s0,
  HTEscape cblock raddr genFaultHandlerReturn
       (fun (m : memory) (s : stack) =>
        handler_final_mem_matches lr lpc m0 m /\
        s = (Vint 1, handlerTag) ::: CRet raddr false false :: s0)
       (fun (m : memory) (s : stack) =>
        (s = s0 /\ handler_final_mem_matches lr lpc m0 m, Success)).
Proof.
  intros.
  unfold genFaultHandlerReturn.
  eapply HTEscape_strengthen_premise.
  - eapply ifNZ_specEscape with (v:=1) (Pf:=fun m s => True); auto; intros.
    eapply ret_specEscape.
    auto.
    false.
  - subst.
    intuition.
    jauto_set_goal; eauto.
Qed.

Lemma genFaultHandlerReturn_specEscape_None: forall raddr s0,
 HTEscape cblock raddr genFaultHandlerReturn
   (fun (m : memory) (s : stack) => m = m0 /\ s = (Vint 0, handlerTag) ::: s0)
   (fun (m : memory) (s : stack) => (m = m0 /\ s = s0, Failure)).
Proof.
  intros.
  unfold genFaultHandlerReturn.
  eapply HTEscape_strengthen_premise.
  - eapply ifNZ_specEscape with (v := 0) (Pt := fun m s => True); auto; intros. 
    + intuition.
    + eapply genError_specEscape. 
  - intros. 
    subst. 
    intuition.
    jauto_set_goal; eauto.
Qed.
 
Lemma faultHandler_specEscape_Some: forall raddr lr lpc,
  valid_address cblock addrTagRes m0 ->
  valid_address cblock addrTagResPC m0 ->
  ar = Some (lpc, lr) ->
  forall s0,
    HTEscape cblock raddr (faultHandler fetch_rule_impl)
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
    HTEscape cblock raddr (faultHandler fetch_rule_impl)
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

Section HandlerCorrect.

Variable get_rule : forall (opcode:OpCode), {n:nat & AllowModify n}.
Definition handler : list Instr := faultHandler get_rule.

Theorem handler_correct_succeed :
  forall opcode vls pcl m raddr s i lr lpc,
  forall (INPUT: cache_hit_mem m (opCodeToZ opcode) (labsToZs vls) (labToZ pcl))
         (RULE: apply_rule (projT2 (get_rule opcode)) pcl vls = Some (lpc,lr)),
    exists m',
    runsToEscape cblock
                 (CState m handler i (CRet raddr false false::s) (0,handlerTag) true)
                 (CState m' handler i s raddr false) /\
    handler_final_mem_matches lpc lr m m'.
Proof.
  intros.
  unfold Concrete.cache_hit_mem in *.
  destruct (Mem.get_frame m cblock) eqn:E; try (intuition; fail).

  assert (valid_address cblock addrTagRes m).
    inv INPUT. inv TAGR. 
    econstructor.
    unfold load; rewrite E.
    edestruct index_list_Z_valid; eauto. 
  assert (valid_address cblock addrTagResPC m).
    inv INPUT. inv TAGRPC. 
    econstructor.
    unfold load; rewrite E.
    edestruct index_list_Z_valid; eauto. 

  edestruct (faultHandler_specEscape_Some get_rule opcode vls pcl m) 
      as [stk1 [cache1 [pc1 [priv1 [[P1 P2] [P3 P4]]]]]]; eauto. 
   eapply init_enough; auto. 
  unfold Concrete.cache_hit_mem; rewrite E; auto.
  apply code_at_id. 
  exists cache1. 
  inversion P3.  subst. 
  intuition.
  apply P4. 
Qed.  
              
Theorem handler_correct_fail : 
  forall opcode vls pcl m raddr s i,
  forall (INPUT: cache_hit_mem m (opCodeToZ opcode) (labsToZs vls) (labToZ pcl))
         (RULE: apply_rule (projT2 (get_rule opcode)) pcl vls = None),
    exists st,
    runsToEscape cblock
                 (CState m handler i (CRet raddr false false::s) (0,handlerTag) true)
                 (CState m handler i st (-1,handlerTag) true).
Proof.
  intros.   
  edestruct (faultHandler_specEscape_None get_rule opcode vls pcl m) with (raddr := (0,0))
      as [stk1 [cache1 [pc1 [priv1 [[P1 P2] [P3 P4]]]]]]; eauto. 
   eapply init_enough; eauto. 
   eapply code_at_id. 
  inv P3. 
  eexists; eauto.
Qed.

End HandlerCorrect.

End TMU.


