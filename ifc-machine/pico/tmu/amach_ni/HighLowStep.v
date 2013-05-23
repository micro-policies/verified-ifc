Require Import ZArith.
Require Import List.

Require Import Utils.
Require Import Lattices.
Require Import AbstractObsEquiv.
Require Import TMUInstr.
Require Import Abstract.
Require Import AbstractCommon.
Require Import AbstractMachine.

Set Implicit Arguments.

Section ParamMachine.

Context {T: Type}.
Context {Latt: JoinSemiLattice T}.

Ltac exploit_low :=
    repeat match goal with
        | [H: low_equiv_list _ (_::_) (_::_) |- _ ] => inv H
        | [H: low_equiv_stkelt _ (AData _) (AData _) |- _ ] => inv H
        | [H: low_equiv_stkelt _ (ARet _ _) (ARet _ _) |- _ ] => inv H
    end.

Ltac spec_pop_return :=
  (exploit @pop_to_return_spec; eauto);
  let stk := fresh "stk" in
  let Hstk := fresh "Hstk" in
  (intros [? [? [? [? [Hstk ?]]]]]);
  match type of Hstk with
    | ?aastk = _ =>
      match goal with
        | [HH: pop_to_return aastk _ |- _ ] => (subst ; move_to_top HH)
      end
  end.

Lemma highlowstep : forall o as1 e as1' as2 e' as2',
  low_equiv_full_state o as1 as2 ->
  ~low_pc o as1 ->
  step_rules as1 e as1' ->
  low_pc o as1' ->
  step_rules as2 e' as2' ->
  low_pc o as2' ->
  low_equiv_full_state o as1' as2'.
Proof.
  intros.
  inv H ; [clear H0 | eelim H0 ; unfold low_pc ; simpl ; auto].

  exploit step_rules_instr; eauto. intros [instr1 Hinstr1].

  (* instr1 is Ret or VRet *)
  destruct instr1;
  try solve [
        (exploit step_rules_non_ret_label_pc ; eauto); try congruence;
        (intros [l' [pc' [Hcont1 Hcont2]]]);
        (eapply low_not_high in Hcont1 ; eauto);
        (rewrite Hcont1 in Flowl1 ; inv Flowl1)].


  Case "P1 is Ret".
      (inv H1 ; try congruence).
      exploit step_rules_instr; eauto. intros [instr2 Hinstr2].

      destruct instr2;
        try solve [
              (exploit step_rules_non_ret_label_pc ; eauto); try congruence;
              (intros [l' [pc' [Hcont1 Hcont2]]]);
              (eapply low_not_high in Hcont1 ; eauto);
              (rewrite Hcont1 in Flowl2 ; inv Flowl2)];
      (inv H3 ; try congruence).

      SCase "P2 is Ret".
          spec_pop_return.
          spec_pop_return.
          exploit @pop_to_return_spec2; eauto. intros H1. inv H1.
          exploit @pop_to_return_spec3; eauto. intros H1. inv H1.
          generalize H11 ; clear H11.
          exploit @pop_to_return_spec2; eauto. intros H1. inv H1.
          exploit @pop_to_return_spec3; eauto. intros H1. inv H1.
          intros.
          rewrite below_lret_adata in LEsH; eauto.
          rewrite below_lret_adata in LEsH; eauto.

          (* both do not return any value *)
          inv H2. inv H4.
          simpl in *. rewrite H2 in *.  rewrite H3 in *.
          exploit_low. inv LEa.
          constructor 2 ; eauto. congruence.

      SCase "P2 is Vret". (* contradiction *)
          spec_pop_return.
          spec_pop_return.
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.
          generalize H11 ; clear H11.
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.
          rewrite below_lret_adata in LEsH; eauto. simpl in LEsH.
          inv H2. rewrite H3 in *.
          rewrite below_lret_adata in LEsH; eauto. simpl in LEsH.
          inv H4. rewrite H2 in *.
          inv LEsH.
          inv H6.

  Case "P1 is VRet".
      (inv H1 ; try congruence).
      exploit step_rules_instr; eauto. intros [instr2 Hinstr2].

      destruct instr2;
        try solve [
              (exploit step_rules_non_ret_label_pc ; eauto); try congruence;
              (intros [l' [pc' [Hcont1 Hcont2]]]);
              (eapply low_not_high in Hcont1 ; eauto);
              (rewrite Hcont1 in Flowl2 ; inv Flowl2)];
      (inv H3 ; try congruence).


      SCase "P2 is Ret".
          spec_pop_return.
          spec_pop_return.
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.
          generalize H11 ; clear H11.
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.
          rewrite below_lret_adata in LEsH; eauto.
          simpl in LEsH.  rewrite below_lret_adata in LEsH; eauto.
          simpl in LEsH.

          inv H2; inv H4.
          rewrite H2 in *.
          rewrite H3 in *.
          inv LEsH. inv H6.


     SCase "P2 is Vret".
          spec_pop_return.
          spec_pop_return.
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.
          generalize H11 ; clear H11.
          exploit @pop_to_return_spec2; eauto. intros. inv H1.
          exploit @pop_to_return_spec3; eauto. intros. inv H1.

          simpl in LEsH. rewrite below_lret_adata in LEsH; eauto.
          rewrite below_lret_adata in LEsH; eauto.
          inv H2 ; inv H4.
          simpl in LEsH.
          rewrite H2 in *; rewrite H3 in *.
          exploit_low. inv LEa.

          constructor 2; eauto.
          constructor; eauto.
          constructor; eauto.
          econstructor 2; eauto with lat.
          congruence.
Qed.

End ParamMachine.
