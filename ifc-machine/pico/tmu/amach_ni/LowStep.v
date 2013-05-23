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

Lemma low_equiv_step_pop_to_return: forall o  stk1 stk2 rstk1 rstk2 ,
  low_equiv_list (low_equiv_stkelt o) stk1 stk2 ->
  pop_to_return stk1 rstk1 ->
  pop_to_return stk2 rstk2 ->
  low_equiv_list (low_equiv_stkelt o) rstk1 rstk2.
Proof.
  induction stk1; intros.
  inv H. inv H0.

  inv H.
  inv H1.
     inv H4. inv H0. eauto.
     inv H0. inv H4. eauto.
Qed.

Lemma lowstep : forall o as1 e as1' as2 e' as2',
  low_equiv_full_state o as1 as2 ->
  low_pc o as1  ->
  step_rules as1 e as1' ->
  step_rules as2 e' as2' ->
  low_equiv_full_state o as1' as2'.
Proof.
  intros. inv H. inv H0. congruence.

  exploit step_rules_instr; eauto. intros [instr1 Hinstr1].
  generalize H1 ; clear H1.
  exploit step_rules_instr; eauto. intros [instr2 Hinstr2].
  intros H1.
  assert (Hinstr: low_equiv_instr o instr1 instr2) by
    (eapply index_list_Z_low_eq  ; eauto).

  inv Hinstr;
    (inv H1 ; try congruence);
    (inv H2 ; try congruence).

  Case "Noop".
  auto.

  Case "Add".
    exploit_low.
    constructor 2; auto.
    eapply join_low_equiv_list; eauto.

  Case "Sub".
    exploit_low.
    constructor 2; auto.
    eapply join_low_equiv_list; eauto.

  Case "Load".
    exploit_low. inv LEa.

    SCase "Load from low addresses".

    assert (Hmemv: low_equiv_atom o  (xv, xl) (xv0, xl0)).
    (eapply index_list_Z_low_eq with (1 := LEm)  ; eauto).

    inv Hmemv; (constructor 2 ; eauto).
      constructor; eauto.
      constructor ; eauto with lat.

    SCase "Load from high addresses".
    constructor 2 ; auto with lat.

  Case "Store".
    exploit_low. simpl in *. allinv. inv H0.
    assert (low_equiv_list (low_equiv_atom o) m' m'0).
    eapply low_equiv_list_update_Z  with (8:= H12) (9:= H15); eauto with lat.
    eapply low_equiv_atom_join_value with (v0:= xv) ; eauto.
    constructor 2; auto.

  Case "Push".
    rewrite H9 in Hinstr1; inv Hinstr1.
    rewrite H8 in Hinstr2; inv Hinstr2.
    constructor 2; eauto.

  Case "Jump".
    exploit_low. inv LEa.
    constructor 2 ; auto with lat.
    constructor; eauto with lat.
    apply below_lret_low_equiv; auto.

  Case "BranchNZ-1".
    exploit_low. inv LEa.
    constructor 2; eauto with lat.
    constructor; eauto with lat.
    apply below_lret_low_equiv; auto.

  Case "BranchNZ-2".
    exploit_low. inv LEa. congruence.
    constructor; eauto with lat.
    apply below_lret_low_equiv; auto.

  Case "BranchNZ-3".
    exploit_low. inv LEa. congruence.
    constructor; eauto with lat.
    apply below_lret_low_equiv; auto.

  Case "BranchNZ-4".
    rewrite H8 in Hinstr2; inv Hinstr2.
    rewrite H9 in Hinstr1; inv Hinstr1.
    exploit_low. inv LEa.
    constructor 2 ; eauto with lat.
    constructor; eauto with lat.
    apply below_lret_low_equiv; auto.

  Case "Call".
     exploit_low.  inv LEa.
     SCase "Low Call".
       constructor 2; auto. eapply join_minimal; eauto.
       rewrite H8 in Hinstr2 ; inv Hinstr2.
       rewrite H9 in Hinstr1 ; inv Hinstr1.
       exploit low_equiv_list_app_left ; eauto.
       exploit low_equiv_list_app_right ; eauto. intros.
       eapply low_equiv_list_app ; eauto.

     SCase "High Call".
       constructor; auto with lat.

       rewrite H8 in Hinstr2 ; inv Hinstr2.
       rewrite H9 in Hinstr1 ; inv Hinstr1.
       exploit low_equiv_list_app_right ; eauto.
       intros Hstk0stk.
       rewrite below_lret_adata ; eauto; [intros; eauto].
       rewrite below_lret_adata ; eauto; [intros; eauto].
       simpl. rewrite Flowl. constructor; eauto.

  Case "Ret".
       spec_pop_return.
       spec_pop_return.
       exploit low_equiv_step_pop_to_return; eauto.
       intros HspecRet.

       exploit_low.
       simpl in *.
       inv LEa.
       constructor 2 ; eauto.
       constructor ; eauto.
       eapply below_lret_low_equiv; eauto.

   Case "VRet".
       spec_pop_return.
       spec_pop_return.
       exploit_low.

       exploit low_equiv_step_pop_to_return; eauto.
       intros HspecRet.  exploit_low. inv H0.
       inv LEa0. inv LEa.
       constructor 2 ; eauto.
       constructor 2 ; eauto with lat.
       constructor; eauto.
       constructor. constructor 2; eauto with lat.
       constructor ; eauto.
       apply below_lret_low_equiv; eauto.
       inv LEa. constructor ; eauto.
       constructor; auto. constructor ; eauto with lat.

   Case " Output".
       exploit_low.
       inv LEa.
       constructor 2 ; eauto.
       constructor 2 ; eauto with lat.
Qed.

End ParamMachine.
