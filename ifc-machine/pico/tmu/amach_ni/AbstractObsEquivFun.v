Require Import Lattices.
Require Import TMUInstr.
Require Import Abstract.
Require Import ZArith.
Require Import AbstractObsEquiv.

Require Import Coq.Bool.Bool.

Set Implicit Arguments.

Open Scope bool_scope.
Open Scope list_scope.

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
    apply flows_antisymm; intuition.
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

Definition low_equiv_stkeltF (o : Label)
           (e1 e2 : @StkElmt Label) : bool :=
  match e1, e2 with
    | AData a1, AData a2 => low_equiv_atomF o a1 a2
    | ARet a1 b1, ARet a2 b2 =>
      low_equiv_atomF o a1 a2 && eqb b1 b2
    | _, _ => false
  end.

Lemma low_equiv_stkeltF_correct :
  forall o e1 e2, low_equiv_stkeltF o e1 e2 = true <->
                  low_equiv_stkelt o e1 e2.
Proof.
  intros o [a1 | a1 []] [a2 | a2 []]; simpl; split;
  intros H; inv H; try constructor;
  try rewrite Bool.andb_true_iff in *;
  try rewrite low_equiv_atomF_correct in *;
  intuition.
Qed.

Definition instr_eqB (i1 i2 : Instr) : bool :=
  match i1, i2 with
  | Noop, Noop => true
  | Add, Add => true
  | Sub, Sub => true
  | Push z1, Push z2 => if Z.eq_dec z1 z2 then true else false
  | Load, Load => true
  | Store, Store => true
  | Jump, Jump => true
  | BranchNZ z1, BranchNZ z2 => if Z.eq_dec z1 z2 then true else false
  | Call n1 b1, Call n2 b2 => beq_nat n1 n2 && eqb b1 b2
  | Ret, Ret => true
  | VRet, VRet => true
  | Halt, Halt => true
  | Output, Output => true
  | _, _ => false
  end.

Lemma instr_eqB_eq : forall i1 i2, instr_eqB i1 i2 = true <-> i1 = i2.
Proof.
  intros [] []; simpl; split; try congruence;
  repeat match goal with
           | |- context[Z.eq_dec ?z1 ?z2] =>
             destruct (Z.eq_dec z1 z2); congruence
         end;
  intros;
  rewrite Bool.andb_true_iff in *;
  rewrite beq_nat_true_iff in *;
  rewrite eqb_true_iff in *; intuition congruence.
Qed.

Lemma low_equiv_instr_eq :
  forall (o : Label) i1 i2, low_equiv_instr o i1 i2 <-> i1 = i2.
Proof.
  intros o [] []; simpl; split;
  intros H; inv H; constructor.
Qed.

Lemma instr_eqB_low_equiv :
  forall (o : Label) i1 i2, instr_eqB i1 i2 = true <-> low_equiv_instr o i1 i2.
Proof.
  intros.
  rewrite low_equiv_instr_eq.
  apply instr_eqB_eq.
Qed.

Fixpoint low_equiv_listF {A} (low_equiv_aF : A -> A -> bool) (l1 l2 : list A) :=
  match l1, l2 with
    | nil, nil => true
    | a1 :: l1', a2 :: l2' =>
      low_equiv_aF a1 a2 && low_equiv_listF low_equiv_aF l1' l2'
    | _, _ => false
  end.

Lemma low_equiv_listF_correct {A} :
  forall (low_equiv_a : A -> A -> Prop)
         (low_equiv_aF : A -> A -> bool)
         (Hleq : forall a1 a2, low_equiv_aF a1 a2 = true <-> low_equiv_a a1 a2)
         (l1 l2 : list A),
    low_equiv_listF low_equiv_aF l1 l2 = true <->
    low_equiv_list low_equiv_a l1 l2.
Proof.
  intros.
  generalize dependent l2;
  induction l1 as [|a1 l1' IH]; destruct l2 as [|a2 l2'];
  simpl; split; try congruence;
  intros H;
  try match goal with
        | H : low_equiv_list _ _ _ |- _ => inv H
      end;
  try rewrite Bool.andb_true_iff in *;
  try constructor; firstorder.
Qed.

Definition low_equiv_full_stateF (o : Label)
           (a1 a2 : @AS Label) : bool :=
  match a1, a2 with
    | AState m1 i1 s1 (pc1, l1),
      AState m2 i2 s2 (pc2, l2) =>
      if l1 <: o then
        atom_eqB (pc1, l1) (pc2, l2) &&
        low_equiv_listF (low_equiv_atomF o) m1 m2 &&
        low_equiv_listF (low_equiv_stkeltF o) s1 s2 &&
        low_equiv_listF instr_eqB i1 i2
      else
        negb (l2 <: o) &&
        low_equiv_listF (low_equiv_atomF o) m1 m2 &&
        low_equiv_listF (low_equiv_stkeltF o)
                        (below_lret o s1) (below_lret o s2) &&
        low_equiv_listF instr_eqB i1 i2
  end.

Lemma low_equiv_full_stateF_correct :
  forall o a1 a2,
    low_equiv_full_stateF o a1 a2 = true <->
    low_equiv_full_state o a1 a2.
Proof.
  intros o [m1 i1 s1 [pc1 l1]] [m2 i2 s2 [pc2 l2]]; simpl;
  destruct (l1 <: o) eqn:Hl1;
  split;
  intros H;
  repeat rewrite Bool.andb_true_iff in *;
  intuition;
  try rewrite atom_eqB_eq in *;
  repeat match goal with
           | H : (_, _) = (_, _) |- _ => inv H
           | H : low_equiv_full_state _ _ _ |- _ => inv H
         end;
  try rewrite negb_true_iff in *;
  try congruence;
  try solve [
        rewrite low_equiv_listF_correct;
        eauto using low_equiv_atomF_correct,
                    low_equiv_stkeltF_correct,
                    instr_eqB_low_equiv
      ];

  econstructor (auto; solve [rewrite <- low_equiv_listF_correct;
    eauto using instr_eqB_low_equiv, low_equiv_stkeltF_correct,
    low_equiv_atomF_correct]).

Qed.

End ObsEquivFun.
