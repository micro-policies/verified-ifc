Require Import List.
Require Import ZArith.

Require Import Utils.
Require Import Lattices.
Require Import CLattices.
Require Import WfCLattices.
Require Import TMUInstr.
Require Import Abstract.
Require Import AbstractCommon.
Require Import Rules.
Require Import QuasiAbstractMachine.
Require Import Concrete.
Require Import ConcreteMachineSmallStep.
Require Import Determinism.
Require Import Refinement.
Require Import CExec.
Require Import FaultRoutine.
Require Import BackwardCommon.

Open Scope Z_scope.

Set Implicit Arguments.

Section CacheMissSimulation.

Context {L: Type}
        {Latt: JoinSemiLattice L}
        {CLatt: ConcreteLattice L}
        {WFCLatt: WfConcreteLattice L Latt CLatt}.

Lemma invalid_pc_no_step :
  forall s1 e s2
         (STEP : cstep s1 e s2)
         (FAIL : fst (pc s1) < 0),
    False.
Proof.
  intros.
  inv STEP; simpl in *;
  unfold read_m in *;
  generalize (Z.ltb_spec0 pcv 0);
  let H := fresh "H" in
  intros H;
  destruct (pcv <? 0); inv H; intuition; congruence.
Qed.

Lemma kernel_run_success_fail_contra :
  forall s1 s21 s22
         (RUN1 : kernel_run_until_user s1 s21)
         (RUN2 : kernel_run s1 s22)
         (FAIL : fst (pc s22) < 0),
    False.
Proof.
  intros.
  induction RUN1; inv RUN2;
  try match goal with
        | [ H1 : cstep ?s _ _,
            H2 : cstep ?s _ _
            |- _ ] =>
          let H := fresh "H" in
          generalize (cmach_priv_determ_state H1 H2);
          intros [? ?]; subst
      end; eauto;
  try match goal with
        | [ H : kernel_run_until_user _ _ |- _ ] =>
          generalize (kernel_run_until_user_l H);
          intros
      end;
  try match goal with
        | [ H : kernel_run _ _ |- _ ] =>
          generalize (kernel_run_l H);
          intros
      end;
  try congruence;
  eauto using invalid_pc_no_step.
Qed.

Lemma kernel_fail_determ :
  forall s1 s21 s22
         (RUN1 : kernel_run s1 s21)
         (FAIL1 : fst (pc s21) < 0)
         (RUN2 : kernel_run s1 s22)
         (FAIL2 : fst (pc s22) < 0),
    s21 = s22.
Proof.
  intros.
  induction RUN1; inv RUN2; trivial;
  try solve [exfalso; eauto using invalid_pc_no_step];
  try match goal with
        | [ H1 : cstep ?s _ _,
            H2 : cstep ?s _ _
            |- _ ] =>
          let H := fresh "H" in
          generalize (cmach_priv_determ_state H1 H2);
          intros [? ?]; subst
      end; eauto.
Qed.

Lemma runsToEscape_determ :
  forall s1 s21 s22
         (RUN1 : runsToEscape s1 s21)
         (RUN2 : runsToEscape s1 s22),
    s21 = s22.
Proof.
  intros.
  inv RUN1; inv RUN2;
  eauto using kernel_run_until_user_determ,
              kernel_fail_determ;
  try solve [exfalso; eauto using kernel_run_success_fail_contra];
  try match goal with
        | [ H : kernel_run_until_user _ _ |- _ ] =>
          generalize (kernel_run_until_user_l H);
          intros
      end;
  try match goal with
        | [ H : kernel_run _ _ |- _ ] =>
          generalize (kernel_run_l H);
          intros
      end;
  try congruence.
Qed.

Lemma configuration_at_miss :
  forall s1 s21 e2 s22
         (MATCH : match_states s1 s21)
         (STEP : cstep s21 e2 s22)
         (PRIV : priv s22 = true),
    exists opcode (vls : Vector.t L (projT1 (fetch_rule_withsig opcode))),
      cache_hit (cache s22) (opCodeToZ opcode)
                (labsToZs vls) (labToZ (snd (apc s1))) /\
      mem s22 = mem s21 /\
      fhdl s22 = fhdl s21 /\
      imem s22 = imem s21 /\
      stk s22 = CRet (pc s21) false false :: stk s21 /\
      pc s22 = (0, handlerTag).
Proof.
  intros.
  inv MATCH.
  inv STEP; simpl in *; try congruence;

  (* Invert some hypotheses *)
  repeat match goal with
           | H : true = false |- _ => inv H
           | H : ?x = ?x |- _ => clear H
           | H : match_stacks _ (_ ::: _) |- _ => inv H
           | H : match_stacks _ (_ ++ _) |- _ =>
             apply match_stacks_args' in H;
             destruct H as [? [? [? [? ?]]]];
             subst
           | a : _,
             H : (_, _) = atom_labToZ ?a |- _ =>
             destruct a; simpl in H; inv H
         end;

    (* For the Load case *)
  try_exploit read_m_labToZ';

  (* For the Ret cases *)
  try_exploit match_stacks_c_pop_to_return;

  try quasi_abstract_labels;

  match goal with
    | H : read_m _ _ = Some ?i |- _ =>
      let oc := eval compute in (opcode_of_instr i) in
      match oc with
        | Some ?oc => (exists oc)
      end
  end;

  exists vls; repeat econstructor; eauto.
Qed.

Lemma update_cache_spec_rvec_cache_hit :
  forall orl l cache cache' op tags pc
         (MATCH : handler_final_mem_matches' orl l cache cache')
         (HIT : cache_hit cache op tags pc),
    cache_hit cache' op tags pc.
Proof.
  intros.
  inv HIT;
  repeat match goal with
           | H : tag_in_mem _ _ _ |- _ =>
             inv H
         end.
  destruct MATCH as [RES UP].
  assert (HIT : exists t, cache_hit_read cache' t (labToZ l)) by
    (destruct orl; eauto).
  destruct HIT as [t []].
  econstructor; eauto; econstructor;
  try solve [rewrite <- UP; eauto; compute; omega];
  repeat match goal with
           | H : tag_in_mem _ _ _ |- _ =>
             inv H
         end;
  eauto.
Qed.

Lemma cache_miss_simulation :
  forall s1 s21 e21 s22 s23
         (MATCH : match_states s1 s21)
         (STEP1 : cstep s21 e21 s22)
         (RUN : kernel_run_until_user s22 s23),
    match_states s1 s23.
Proof.
  intros.
  exploit kernel_run_until_user_l; eauto.
  intros PRIV.
  exploit configuration_at_miss; eauto.
  intros [op [vls [HIT EQS]]].
  destruct s22; simpl in EQS, PRIV; subst.
  inv MATCH; simpl.
  intuition. subst.
  destruct (apply_rule (projT2 (fetch_rule_withsig op)) vls (snd apc))
    as [[orl rpcl]|] eqn:E.
  - exploit handler_correct_succeed; eauto.
    intros [cache' [ESCAPE1 MATCH']].
    exploit rte_success; eauto.
    intros ESCAPE2.
    unfold Refinement.faultHandler, handler in *.
    generalize (runsToEscape_determ ESCAPE1 ESCAPE2).
    intros H. subst.
    constructor; eauto.
    simpl in *.
    exploit update_cache_spec_rvec_cache_hit; eauto.
    clear HIT. intros HIT.
    intros op' vls' pcl' HIT'.
    generalize (cache_hit_unique HIT HIT').
    intros [E1 [E2 E3]].
    apply Refinement.opCodeToZ_inj in E1. subst.
    apply labToZ_inj in E3. subst.
    apply labsToZs_inj in E2.
    + subst. rewrite E.
      destruct MATCH'. trivial.
    + destruct op'; simpl; omega.
  - exploit handler_correct_fail; eauto.
    simpl in *.
    intros [stk' [tag' ESCAPE1]].
    inv ESCAPE1.
    + apply kernel_run_until_user_r in STAR. simpl in STAR. congruence.
    + exfalso.
      eapply kernel_run_success_fail_contra; eauto.
Qed.

End CacheMissSimulation.
