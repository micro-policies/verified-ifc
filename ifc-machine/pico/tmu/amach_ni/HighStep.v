Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import Lattices.
Require Import AbstractObsEquiv.
Require Import TMUInstr.
Require Import Abstract.
Require Import Rules.
Require Import AbstractCommon.
Require Import AbstractMachine.
Require Import LNIwithEvents.
Require TINI.

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

Lemma highstep : forall o as1 e as1',
  ~low_pc o as1 ->
  step_rules as1 e as1' ->
  ~low_pc o as1' ->
  low_equiv_full_state o as1 as1'.
Proof.
  intros.
  destruct as1. destruct apc.
  assert (t <: o = false). destruct (flows_dec t o); auto.
  unfold low_pc in * ; simpl in *. congruence.
  clear H. inv H0; eauto with lat.

  Case "Store".
    destruct (flows_dec ml o).
    SCase "ml <: o = true".
      assert (t <: o = true). eauto with lat. congruence.
    SCase "ml <: o = false".
      assert (low_equiv_list (low_equiv_atom o) m' amem).
      eapply update_list_Z_high with (4:= H10) (5:= H12); eauto with lat.
      constructor ; eauto. symmetry ; auto.

  Case "Call".
    constructor; eauto with lat.
    simpl.
    do 2
       (erewrite below_lret_adata; eauto;
        try (intros; eapply in_rev in H ; eauto)).
    simpl. rewrite H2; auto.

   Case "Ret".
    spec_pop_return.
    exploit @pop_to_return_spec2; eauto. intros. inv H0.
    exploit @pop_to_return_spec3; eauto. intros. inv H0.
    destruct (flows_dec pcl' o) ; auto. eelim H1.
        eelim H1 ; unfold low_pc ; simpl ; auto.

        constructor ; eauto.
        rewrite below_lret_adata; eauto.
        simpl. rewrite e.
        auto.

   Case "VRet".
    spec_pop_return.
    exploit @pop_to_return_spec2; eauto. intros. inv H0.
    exploit @pop_to_return_spec3; eauto. intros. inv H0.

    destruct (flows_dec pcl' o); auto.
    eelim H1 ; unfold low_pc ; simpl ; auto.
    (constructor; eauto). simpl.
    rewrite below_lret_adata; eauto.  simpl.
    rewrite e; auto.
Qed.

End ParamMachine.
