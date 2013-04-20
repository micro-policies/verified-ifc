Require Import ZArith.
Require Import List.
Require Import Utils.
Import ListNotations.
Require Vector.

Require Import LibTactics.
Require Import TMUInstr.
Require Import Lattices.
Require Import Concrete.
Require Import ConcreteMachineSmallStep.
Require Import Rules.
Require Import CLattices.
Require Import CodeSpecs. 
Require Import CodeGen.
Require Import CLattices.
Require Import WfCLattices.

Section TMU. 

Open Local Scope Z_scope.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}
        {WFCLatt: WfConcreteLattice T Latt CLatt}. 


(* --------------------- TMU Fault Handler code ----------------------------------- *)

(* Compilation of rules *)

Definition genError :=
  push' (-1) ++ [Jump].

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

Fixpoint genScond {n:nat} (s: rule_scond n) : code :=
  match s with
  | A_True => genTrue
  | A_LE e1 e2 => genExpr e2 ++ genExpr e1 ++ genFlows
  | A_And s1 s2 => genScond s2 ++ genScond s1 ++ genAnd 
  | A_Or s1 s2 => genScond s2 ++ genScond s1 ++ genOr 
  end.


Definition genApplyRule {n:nat} (am:AllowModify n): code :=
  ite (genScond (allow am))
      ((genExpr (labResPC am)) ++
       some
         match (labRes am) with
         | Some lres => some (genExpr lres)
         | None      => none
         end
      )
      none.

Section FaultHandler.

Definition genCheckOp (op:OpCode): code :=
  genTestEqual (push' (opCodeToZ op)) (loadFrom addrOpLabel).

Definition fetch_rule_impl_type: Type := forall (opcode:OpCode),  {n:nat & AllowModify n}.
Variable fetch_rule_impl: fetch_rule_impl_type.
Definition opcodes := 
  [OpNoop; OpAdd; OpSub; OpPush; OpLoad; OpStore; OpJump; OpBranchNZ; OpCall; OpRet; OpVRet].
Definition genApplyRule' op := genApplyRule (projT2 (fetch_rule_impl op)).
(* Fault handler that puts results on stack. *)
Definition genFaultHandlerStack: code :=
  indexed_cases nop genCheckOp genApplyRule' opcodes.

(* Write fault handler results to memory. *)
Definition genFaultHandlerMem: code :=
  ifNZ (ifNZ (storeAt addrTagRes) nop ++
        storeAt addrTagResPC ++
        genTrue)
       genFalse.

Definition faultHandler: code :=
  genFaultHandlerStack ++
  genFaultHandlerMem ++
  ifNZ [Ret] genError.

(* NC: or

   ite (genFaultHandlerStack ++ genFaultHandlerMem)
        [Ret]
        genError.
*)

End FaultHandler.

(*
Definition genRule {n:nat} (am:AllowModify n) (opcode:Z) : code :=
  let (allow, labresopt, labrespc) := am in 
  let body := 
    genScond allow ++
    [BranchNZ (Z.of_nat(length(genError)) +1)] ++
    genError ++ 
    genExpr labrespc ++
    storeAt addrTagResPC ++ 
    match labresopt with 
    | Some labres =>
      genExpr labres ++
      storeAt addrTagRes
    | None => []
    end ++
    [Ret] in
  (* test if correct opcode; if not, jump to end to fall through *)    
  branchIfLocNeq addrOpLabel opcode (Z.of_nat (length body)) ++ body.


Definition faultHandler (fetch_rule_impl: forall (opcode:OpCode),  AllowModify (labelCount opcode)) : code :=
  let gen (opcode:OpCode) := genRule (fetch_rule_impl opcode) (opCodeToZ opcode) in
  gen OpNoop ++
  gen OpAdd ++ 
  gen OpSub ++
  gen OpPush ++
  gen OpLoad ++
  gen OpStore ++
  gen OpJump ++
  gen OpBranchNZ ++
  gen OpCall ++
  gen OpRet ++
  gen OpVRet ++
  genError.
*)


(* ================================================================ *)
(* Fault-handler Code Specifications                                *)

(* Connecting vectors of labels to triples of tags. *)

Section Glue.

Import Vector.VectorNotations.

Local Open Scope nat_scope.

(* Old definition; replaced below. 
Definition glue {n:nat} (vls :Vector.t T n) : (option T * option T * option T) :=
match vls with
| [] => (None,None,None)
| [t1] => (Some t1, None,None)
| [t1; t2] => (Some t1, Some t2, None)
| (t1::(t2::(t3::_))) => (Some t1, Some t2, Some t3)
end. 
*)

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
  index_list_Z addrOpLabel m = Some(opcode,handlerTag)
  /\ index_list_Z addrTag1 m = Some (tag1,handlerTag)
  /\ index_list_Z addrTag2 m = Some (tag2,handlerTag)
  /\ index_list_Z addrTag3 m = Some (tag3,handlerTag)
  /\ index_list_Z addrTagPC m = Some (pctag,handlerTag)
.

(* APT: Just a little sanity check that these definitions are somewhat coherent. *)
Lemma init_init: forall (m:memory)  op ts tpc, cache_hit m op ts tpc ->
let '(l1,l2,l3) := ts in
handler_initial_mem_matches op l1 l2 l3 tpc m.
Proof.
  intros.
  inv H. inv OP. inv TAG1. inv TAG2. inv TAG3. inv TAGPC. 
  econstructor; eauto.
Qed.

(*
(* Connecting to the definition used in FaultRoutine.v : *)
Lemma init_enough0: forall {n} (vls:Vector.t T n) m opcode opls pcl,
    glued vls opls ->                      
    cache_hit m opcode opls pcl ->
    handler_initial_mem_matches 
      opcode
      (nth_order_option vls 0)
      (nth_order_option vls 1)
      (nth_order_option vls 2)
      pcl m.
Proof.
  intros. 
  inv H0. destruct opls as [[? ?] ?]. inv MVEC. inv OP. inv TAG1. inv TAG2. inv TAG3. inv TAGPC.  
  inv H;
    match goal with H: existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end; subst;  
    (* inj_pair2 is an axiom !!!!!!! *)
  unfold handler_initial_mem_matches; simpl; intuition. 
Qed.
*)

(* Connecting to the definition used in ConcreteMachine.v *)
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
  econstructor; eauto. 
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

Lemma genVar_spec:
  forall v l,
    eval_var v = l ->
    forall s0,
      HT   (genVar v)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (labToZ l, handlerTag) :: s0).
Proof.
  intros v l Heval_var s0.
  destruct v; simpl; eapply loadFrom_spec;
  simpl in *; unfold handler_initial_mem_matches in *.

  (* Most of the cases are very similar ... *)
  Ltac nth_order_case k :=
    erewrite (nth_order_valid n vls k) in *;
    intuition;
    subst; auto;
    eauto.
  nth_order_case 0%nat.
  nth_order_case 1%nat.
  nth_order_case 2%nat.

  intuition.
  subst; auto.
  eauto.
Qed.


Lemma genExpr_spec: forall (e: rule_expr n),
  forall l,
    eval_expr eval_var e = l ->
    forall s0,
      HT   (genExpr e)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (labToZ l, handlerTag) :: s0).
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
Qed.


Lemma genScond_spec: forall (c: rule_scond n),
  forall b,
    eval_cond eval_var c = b ->
    forall s0,
      HT   (genScond c)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (boolToZ b, handlerTag) :: s0).
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

  (* And *)
  eapply HT_compose.
  eapply IHc2.
  eauto.
  eapply HT_compose.
  eapply IHc1.
  eauto.
  eapply genAnd_spec.

  (* Or *)
  eapply HT_compose.
  eapply IHc2.
  eauto.
  eapply HT_compose.
  eapply IHc1.
  eauto.
  eapply genOr_spec.
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

Lemma genApplyRule_spec_Some_Some:
  forall l1 l2,
    apply_rule am vls pcl = Some (Some l1, l2) ->
    forall s0,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (        1, handlerTag) :: (* [Some (...)] *)
                           CData (        1, handlerTag) :: (* [Some l1] *)
                           CData (labToZ l1, handlerTag) ::
                           CData (labToZ l2, handlerTag) :: s0).
Proof.
  introv Happly. intros.
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.
  cases (labRes am); try (solve [false; auto]).
  inversion Happly; subst.

  eapply ite_spec_specialized with (v:=boolToZ true).
    eapply genScond_spec; auto.

    intros.
    eapply HT_compose.

      apply genExpr_spec.
      eauto.

      eapply some_spec.
      eapply some_spec.
      eapply genExpr_spec.
      eauto.

    intros; false; omega.
Qed.

Lemma genApplyRule_spec_Some_None:
  forall l2,
    apply_rule am vls pcl = Some (None, l2) ->
    forall s0,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (        1, handlerTag) :: (* [Some (...)] *)
                           CData (        0, handlerTag) :: (* [None] *)
                           CData (labToZ l2, handlerTag) :: s0).
Proof.
  introv Happly. intros.
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.
  cases (labRes am); try (solve [false; auto]).
  inversion Happly; subst.

  eapply ite_spec_specialized with (v:=boolToZ true).
    eapply genScond_spec; auto.

    intros.
    eapply HT_compose.

      apply genExpr_spec.
      eauto.

      eapply some_spec.
      eapply none_spec.

    intros; false; omega.
Qed.

Lemma genApplyRule_spec_None:
    apply_rule am vls pcl = None ->
    forall s0,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (0, handlerTag) :: s0). (* [None] *)
Proof.
  introv Happly. intros.
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.

  eapply ite_spec_specialized with (v:=boolToZ false); intros.
    eapply genScond_spec; auto.

    unfold boolToZ in *; false; omega.

    apply none_spec.
Qed.

Definition listify_apply_rule
  (ar: option (option T * T)) (s0: stack): stack
:=
  match ar with
  | None                => CData (0, handlerTag) :: s0
  | Some (None,    lpc) => CData (1, handlerTag) ::
                           CData (0, handlerTag) ::
                           CData (labToZ lpc, handlerTag) :: s0
  | Some (Some lr, lpc) => CData (1, handlerTag) ::
                           CData (1, handlerTag) ::
                           CData (labToZ lr, handlerTag) ::
                           CData (labToZ lpc, handlerTag) :: s0
  end.

Lemma genApplyRule_spec:
  forall ar,
    apply_rule am vls pcl = ar ->
    forall s0,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = listify_apply_rule ar s0).
Proof.
  intros.
  case_eq ar; intros p ?; subst.
  - destruct p as [o l2]; case_eq o; intros l1 ?; subst.
    + eapply genApplyRule_spec_Some_Some; eauto.
    + eapply genApplyRule_spec_Some_None; eauto.
  - eapply genApplyRule_spec_None; eauto.
Qed.

Lemma genApplyRule_spec_GT:
  forall ar,
    apply_rule am vls pcl = ar ->
      GT (genApplyRule am)
         (fun m s => m = m0)
         (fun m0' s0 m s => m = m0 /\
                            s = listify_apply_rule ar s0).
Proof.
  unfold GT; intros.
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
                  s = (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode)
                      ,handlerTag) ::: s0).
Proof.
  intros.
  unfold genCheckOp.
  eapply genTestEqual_spec.
  eapply push_spec''.
  intros.
  eapply loadFrom_spec.
  unfold handler_initial_mem_matches in *.
  iauto.
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

Variable ar: option (option T * T).
Hypothesis H_apply_rule: apply_rule am vls pcl = ar.

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
    GT_guard_v (genB opcode')
               (fun m s => m = m0)
               (genV opcode')
               (genQ opcode').
Proof.
  (* NC: This proof is ugly ... not sure where I've gone wrong, but I
  have ... *)
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
  intuition; solve
    [ eapply genCheckOp_spec_GT_push_v
    | eapply genApplyRule'_spec_GT_guard_v ].
Qed.

Lemma genFaultHandlerStack_spec_GT:
  GT (genFaultHandlerStack fetch_rule_impl)
     (fun m s => m = m0)
     (fun m0' s0 m s => m = m0 /\
                        s = listify_apply_rule ar s0).
Proof.
  intros.
  eapply GT_consequence'.
  unfold genFaultHandlerStack.
  eapply indexed_cases_spec with (Qnil:=Qnil).
  - Case "default case that we never reach".
    unfold GT; intros.
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
    cases opcode;
      unfold genV, genQ; subst; simpl; intuition.
Qed.

(* Under our assumptions, [genFaultHandlerStack] just runs the appropriate
   [genApplyRule]: *)
Lemma genFaultHandlerStack_spec:
    forall s0,
      HT   (genFaultHandlerStack fetch_rule_impl)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = listify_apply_rule ar s0).
Proof.
  intros.
  eapply HT_consequence'.
  eapply genFaultHandlerStack_spec_GT.
  iauto.
  simpl; iauto.
Qed.


(* XXX: NC: not sure which spec I'm supposed to prove, but
[handler_final_mem_matches'] is the only one used, so try to get there
first? *)

Lemma genFaultHandlerMem_spec_Some_None: forall lpc,
  valid_address addrTagResPC m0 ->
  ar = Some (None, lpc) ->
  forall s0,
    HT genFaultHandlerMem
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => upd_m addrTagResPC (labToZ lpc,handlerTag) m0 =
                     Some m /\
                   s = (1,handlerTag) ::: s0).
Proof.
  introv Hvalid Har_eq; intros.
  unfold listify_apply_rule.
  rewrite Har_eq.
  unfold genFaultHandlerMem.

  (* Need to exploit early so that existentials can be unified against
  vars introduced here *)
  exploit valid_store; eauto.
  intro H; destruct H.

  eapply HT_strengthen_premise.
  eapply ifNZ_spec_NZ with (v:=1).
  eapply HT_compose_bwd.
  eapply HT_compose_bwd.
  eapply genTrue_spec_wp.
  eapply storeAt_spec_wp.
  eapply ifNZ_spec_Z with (v:=0).
  eapply nop_spec_wp.

  omega.
  omega.
  simpl; intuition; subst; jauto.
Qed.

Lemma genFaultHandlerMem_spec_Some_Some: forall lr lpc,
  valid_address addrTagRes m0 ->
  valid_address addrTagResPC m0 ->
  ar = Some (Some lr, lpc) ->
  forall s0,
    HT genFaultHandlerMem
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s =>
        (exists m', upd_m addrTagRes (labToZ lr,handlerTag) m0
                    = Some m'
                 /\ upd_m addrTagResPC (labToZ lpc,handlerTag) m'
                    = Some m)
        /\ s = (1,handlerTag) ::: s0).
Proof.
  introv HvalidRes HvalidResPC Har_eq; intros.
  unfold listify_apply_rule.
  rewrite Har_eq.
  unfold genFaultHandlerMem.

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
  eapply ifNZ_spec_NZ with (v:=1).
  eapply storeAt_spec_wp.

  omega.
  omega.
  simpl; intuition; subst; jauto.
  eauto.
Qed.

Lemma genFaultHandlerMem_spec_None:
  ar = None ->
  forall s0,
    HT genFaultHandlerMem
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => m = m0 /\
                   s = (0,handlerTag) ::: s0).
Proof.
  introv Har_eq; intros.
  unfold listify_apply_rule.
  rewrite Har_eq.
  unfold genFaultHandlerMem.

  eapply HT_strengthen_premise.
  eapply ifNZ_spec_Z with (v:=0).
  eapply genFalse_spec.

  reflexivity.
  jauto.
Qed.

(* The irrelevant memory never changes *)
Lemma genFaultHandlerMem_update_cache_spec_rvec:
  valid_address addrTagRes m0 ->
  valid_address addrTagResPC m0 ->
  forall s0,
    HT genFaultHandlerMem
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => update_cache_spec_rvec m0 m).
Proof.
  intros.
  unfold update_cache_spec_rvec in *.

  cases ar as Eq_ar.
  destruct p.
  cases o.

  + eapply HT_weaken_conclusion;
    rewrite <- Eq_ar in *.

    eapply genFaultHandlerMem_spec_Some_Some; eauto.

    simpl.
    intros;

    jauto_set_hyps; intros.
    eapply transitivity.
    eapply update_list_Z_spec2; eauto.
    eapply update_list_Z_spec2; eauto.

  + eapply HT_weaken_conclusion;
    rewrite <- Eq_ar in *.

    eapply genFaultHandlerMem_spec_Some_None; eauto.

    simpl.
    intros;

    jauto_set_hyps; intros.
    eapply update_list_Z_spec2; eauto.

  + eapply HT_weaken_conclusion;
    rewrite <- Eq_ar in *.

    eapply genFaultHandlerMem_spec_None; eauto.

    simpl; intuition; subst; auto.
Qed.

(* DD: yet another version *)
(* NC: used in [handler_correct_succeed] below. *)
Definition handler_final_mem_matches' (olr: option T) (lpc: T) (m: memory) (m': memory) :Prop :=
  (match olr with
     | Some lr => cache_hit_read m' (labToZ lr) (labToZ lpc)
     | None => exists t, cache_hit_read m' t (labToZ lpc)
   end)
  (* Nothing else changed *)
  /\ update_cache_spec_rvec m m'.

(* XXX: NC: is this actually true? *)
Conjecture valid_address_index_list_Z: forall a m,
  valid_address a m ->
  exists z, index_list_Z a m = Some (z, handlerTag).

Lemma genFaultHandlerMem_spec_Some: forall olr lpc,
  valid_address addrTagRes m0 ->
  valid_address addrTagResPC m0 ->
  ar = Some (olr, lpc) ->
  forall s0,
    HT genFaultHandlerMem
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => handler_final_mem_matches' olr lpc m0 m
                   /\ s = (1,handlerTag) ::: s0).
Proof.
  introv HvalidRes HvalidResPC Har_eq; intros.
  eapply HT_split_conclusion.
  { unfold handler_final_mem_matches'.
    eapply HT_split_conclusion.
    { cases olr; subst olr.
      { eapply HT_weaken_conclusion.
        + eapply genFaultHandlerMem_spec_Some_Some;  eauto.
        + unfold handler_final_mem_matches'. intuition.
          - (* rewrite (ZToLab_labToZ_id t). *)
            (* rewrite (ZToLab_labToZ_id lpc). *)
            eapply chr_uppriv.
            (* Ugh ... *)
            * eapply tim_intro.
              jauto_set_hyps; intros.
              eapply transitivity.
              symmetry.
              eapply update_list_Z_spec2.
              eauto.
              unfold addrTagRes, addrTagResPC; omega.
              eapply update_list_Z_spec; eauto.
            * eapply tim_intro.
              jauto_set_hyps; intros.
              eapply update_list_Z_spec; eauto.
      }
      { eapply HT_weaken_conclusion.
        + eapply genFaultHandlerMem_spec_Some_None;  eauto.
        + unfold handler_final_mem_matches'. intuition.
          - destruct (valid_address_index_list_Z _ _ HvalidRes) as [z ?].
            exists (* ZToLab *)  z.
            (* rewrite (ZToLab_labToZ_id lpc). *)
            eapply chr_uppriv.
            (* Ugh ... *)
            * eapply tim_intro.
              eapply transitivity.
              symmetry.
              eapply update_list_Z_spec2.
              eauto.
              unfold addrTagRes, addrTagResPC; omega.
              eauto.
            * eapply tim_intro.
              eapply update_list_Z_spec; eauto.
      }
    }
    - eapply genFaultHandlerMem_update_cache_spec_rvec; eauto.
  }
  - cases olr; subst olr; eapply HT_weaken_conclusion.
    + eapply genFaultHandlerMem_spec_Some_Some; eauto.
    + intuition; jauto.
    + eapply genFaultHandlerMem_spec_Some_None; eauto.
    + intuition; jauto.
Qed.

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
        inversion H0; subst; jauto.
Qed.

Definition genFaultHandlerReturn: code := ifNZ [Ret] genError.

Lemma genFaultHandlerReturn_specEscape_Some: forall raddr olr lpc,
  fst raddr > 0 ->
  forall s0,
  HTEscape raddr genFaultHandlerReturn
       (fun (m : memory) (s : stack) =>
        handler_final_mem_matches' olr lpc m0 m /\
        s = (1, handlerTag) ::: CRet raddr false false :: s0)
       (fun (m : memory) (s : stack) =>
        (s = s0 /\ handler_final_mem_matches' olr lpc m0 m, Success)).
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

Lemma faultHandler_specEscape_Some: forall raddr olr lpc,
  fst raddr > 0 ->
  valid_address addrTagRes m0 ->
  valid_address addrTagResPC m0 ->
  ar = Some (olr, lpc) ->
  forall s0,
    HTEscape raddr (faultHandler fetch_rule_impl)
             (fun m s => m = m0 /\
                         s = (CRet raddr false false::s0))
             (fun m s => ( s = s0 /\
                           handler_final_mem_matches' olr lpc m0 m
                         , Success )).
Proof.
  intros.
  unfold faultHandler.
  eapply HTEscape_compose.
  - eapply genFaultHandlerStack_spec.
  - eapply HTEscape_compose.
    + eapply genFaultHandlerMem_spec_Some; eauto.
    + eapply genFaultHandlerReturn_specEscape_Some; auto.
Qed.

End FaultHandlerSpec.

End TMUSpecs.

(*
(* Relate abstact rv to final handler memory. *)
Definition handler_final_mem_matches (rv: (option T * T)) (m: @memory T) (m': memory) : Prop :=
  let (olr,lpc) := rv in
  (match olr with
   | Some lr => tag_in_mem m' addrTagRes (labToZ lr)
   | None => index_list_Z addrTagRes m' = index_list_Z addrTagRes m 
   (* DD: not sure we need that precision for the None case.  *)
   end) 
  /\ tag_in_mem m' addrTagResPC (labToZ lpc)
  /\ update_cache_spec_rvec m m'.
*)

Conjecture handler_correct : 
  forall (fetch_rule_impl : (forall (opcode:OpCode), {n:nat & AllowModify n})),
  forall  opcode vls pcl m retaddr c imem fhdl s,
    let am := fetch_rule_impl opcode in
    let handler := faultHandler fetch_rule_impl in
    cache_hit c (opCodeToZ opcode) (labsToZs vls) (labToZ pcl) ->
    exists c' st pc priv, 
      runsToEscape (CState c m fhdl imem (CRet retaddr false false::s) (0,handlerTag) true)
                   (CState c' m fhdl imem st pc priv) /\ 
      match apply_rule (projT2 am) vls pcl with
        | Some (olr,lpc) => handler_final_mem_matches' olr lpc c c' 
                     /\ pc = retaddr
                     /\ st = s
                     /\ priv = false
        | None => c' = c /\ pc = (-1,handlerTag) /\ priv = true
    end.

(* TODO for Nathan: relate [runsToEscape] to [runsToEnd].*)

Section HandlerCorrect.
(* DD: Hopefully easier to parse *)

Variable get_rule : forall (opcode:OpCode), {n:nat & AllowModify n}.
Definition handler : list Instr := faultHandler get_rule.

(* NC: appears this is the currently used conjecture, so prove this
first. *)
Theorem handler_correct_succeed :
  forall opcode vls pcl c m raddr s i olr lpc,
  forall (INPUT: cache_hit c (opCodeToZ opcode) (labsToZs vls) (labToZ pcl))
         (RULE: apply_rule (projT2 (get_rule opcode)) vls pcl = Some (olr,lpc)),
    exists c',
    runsToEscape (CState c m handler i (CRet raddr false false::s) (0,handlerTag) true)
                 (CState c' m handler i s raddr false) /\
    handler_final_mem_matches' olr lpc c c'.
Proof.
  intros.
  (* NC: XXX: believe I need this for [ret_specEscape], but I should
  double check ... *)
  assert (fst raddr > 0) by admit.

  (* NC: I definitely need these to reason about modifying these
  addresses. *)
  assert (valid_address addrTagRes c) by admit.
  assert (valid_address addrTagResPC c) by admit.

  (* NC: not sure how to instantiate here. *)
  admit.
  (*
  exploit (faultHandler_specEscape_Some get_rule opcode vls pcl c); eauto.
  - eapply init_enough; auto.
  - intuition. jauto_set_hyps; intros.
  *)
Qed.
              
Conjecture handler_correct_fail : 
  forall opcode vls pcl c m raddr s i,
  forall (INPUT: cache_hit c (opCodeToZ opcode) (labsToZs vls) (labToZ pcl))
         (RULE: apply_rule (projT2 (get_rule opcode)) vls pcl = None),
    exists st,
    runsToEscape (CState c m handler i (CRet raddr false false::s) (0,handlerTag) true)
                 (CState c m handler i st (-1,handlerTag) true).

(*  We also have the following: 
    - the handler code terminates DONE
    - it does not modifies the user program DONE (* SEE COMMENT BELOW *)
    - it preserves the handler code itself DONE  (* SEE COMMENT BELOW *)

   In fact, preservation of all code (user and handler) is actually a
   universal property of the machines, and should really be built into
   their definition, i.e. imem should not be part of the state.
*)

End HandlerCorrect.

End TMU.
