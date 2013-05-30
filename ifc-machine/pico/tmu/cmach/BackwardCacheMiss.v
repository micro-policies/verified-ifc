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

(** The fault handler code and its correctness *)
Definition fetch_rule_withsig :=
  (fun opcode => existT _ (labelCount opcode) (fetch_rule opcode)).
Definition faultHandler := faultHandler fetch_rule_withsig.

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

Lemma cache_configuration_at_miss :
  forall s1 s21 e2 s22
         (MATCH : match_states s1 s21)
         (STEP : cstep s21 e2 s22)
         (PRIV : priv s22 = true),
    exists opcode (vls : Vector.t L (labelCount opcode)),
      cache_hit (cache s22) (opCodeToZ opcode)
                (labsToZs vls) (labToZ (snd (apc s1))).
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

Lemma cache_miss_simulation :
  forall s1 s21 e21 s22 s23
         (MATCH : match_states s1 s21)
         (STEP1 : cstep s21 e21 s22)
         (RUN : kernel_run_until_user s22 s23),
    match_states s1 s23.
Proof.
  intros.
  exploit cache_configuration_at_miss;
  eauto using kernel_run_until_user_l.
  intros [op [vls HIT]].
  destruct (apply_rule (projT2 (fetch_rule_withsig op)) vls (snd (apc s1))) eqn:E.
Admitted.

End CacheMissSimulation.
