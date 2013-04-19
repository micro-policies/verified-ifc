Require Import Lattices.
Require Import TMUInstr.
Require Import Abstract.
Require Import ZArith.
Require Import AbstractObsEquiv.

Set Implicit Arguments.

Open Scope bool_scope.

Section ObsEquivFun.

Context {Label: Type}.
Context {Latt: JoinSemiLattice Label}.

Definition lab_eqB (l1 l2 : Label) : bool :=
  flows l1 l2 && flows l2 l1.

Lemma lab_eqB_eq : forall l1 l2, lab_eqB l1 l2 = true <-> l1 = l2.
Proof.
  intros l1 l2.
  unfold lab_eqB.
  split; intros H.
  - rewrite Bool.andb_true_iff in H.
    apply flows_antisymm; tauto.
  - subst. rewrite flows_refl. reflexivity.
Qed.

Definition atom_eqB (a1 a2 : @Atom Label) : bool :=
  if Z.eq_dec (fst a1) (fst a2) then
    lab_eqB (snd a1) (snd a2)
  else false.

Definition atom_eqB_eq : forall a1 a2, atom_eqB a1 a2 = true <-> a1 = a2.
Proof.
  intros [v1 l1] [v2 l2].
  unfold atom_eqB.
  simpl.
  destruct (Z.eq_dec v1 v2) as [H | H];
  subst; split; intros H'; try congruence.
  - apply lab_eqB_eq in H'. congruence.
  - inversion H'; subst.
    rewrite lab_eqB_eq. reflexivity.
Qed.

Definition low_equiv_atomF (o : Label) (a1 a2 : @Atom Label) : bool :=
  if snd a1 <: o then
    atom_eqB a1 a2
  else negb (snd a2 <: o).

Definition low_equiv_atomF_correct :
  forall o a1 a2,
    low_equiv_atomF o a1 a2 = true <-> low_equiv_atom o a1 a2.
Proof.
  intros o [v1 l1] [v2 l2].
  unfold low_equiv_atomF.
  simpl.
  destruct (l1 <: o) eqn: Hl1;
  simpl; split; intros H'; try congruence.
  - rewrite atom_eqB_eq in H'.
    inv H'.
    reflexivity.
  - inv H'; try congruence.
    rewrite atom_eqB_eq. reflexivity.
  - rewrite Bool.negb_true_iff in H'.
    constructor; trivial.
  - inv H'; try congruence.
    rewrite Bool.negb_true_iff. trivial.
Qed.

End ObsEquivFun.
