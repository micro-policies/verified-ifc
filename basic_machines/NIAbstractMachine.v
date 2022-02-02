Require Import Coq.Strings.String. Open Scope string_scope.
Require Import ZArith.
Require Import Lia.
Require Import List.

Require Setoid.
Require RelationClasses.
Require Import Relations.

Require Import Utils.
Require Import Lattices.
Require Import Instr.
Require Import AbstractCommon.
Require Import AbstractMachine.
Require TINI.

(** The Abstract Machine satisfies TINI. *)

Set Implicit Arguments.

Section ObsEquiv.

Context {Label: Type}.
Context {Latt: JoinSemiLattice Label}.

(** * Low equivalence relations *)
Definition low_pc (o: Label) (s: AS) : Prop :=
  snd (apc s) <: o = true.

Lemma low_pc_dec: forall o s, {low_pc o s}+{~ low_pc o s}.
Proof.
  intros. unfold low_pc.
  destruct (flows (snd (apc s)) o); auto.
Qed.

Inductive low_equiv_atom (o: Label) : relation (@Atom Label) :=
| le_a_low : forall l v, l <: o = true -> low_equiv_atom o (v,l) (v,l)
| le_a_high: forall l1 l2 v1 v2,
  l1 <: o = false ->
  l2 <: o = false ->
  low_equiv_atom o (v1,l1) (v2,l2).
Hint Constructors low_equiv_atom : core.

Global Instance low_atom (o: Label) : @Equivalence (@Atom Label) (low_equiv_atom o).
Proof.
  constructor.
  (* reflexive *) intro x. destruct x;
  destruct (flows l o) eqn:?; auto.
  (* symmetric *) intros x y Hxy. inv Hxy ; auto.
  (* transitive *) intros x y z Hxy Hyz.
  inv Hxy; auto. inv Hyz ; auto.
Qed.

Hint Extern 1 =>
  match goal with
    | |- low_equiv_atom _ _ _ => reflexivity
  end : core.


Lemma low_equiv_atom_join_value:
  forall o v1 v0 v v2 vl vl0  vl2 vl1,
    low_equiv_atom o (v1, vl) (v, vl0) ->
    low_equiv_atom o (v2, vl2) (v0, vl1) ->
    low_equiv_atom o (v1, vl \_/ vl2) (v, vl0 \_/ vl1).
Proof.
  intros.
  inv H; inv H0; econstructor; eauto with lat.
Qed.

Inductive low_equiv_stkelt (o: Label) : @StkElmt Label -> @StkElmt Label -> Prop :=
| le_data : forall a1 a2
  (LEa: low_equiv_atom o a1 a2),
  low_equiv_stkelt o (AData a1) (AData a2)
| le_aret : forall a1 a2 b
  (LEa: low_equiv_atom o a1 a2),
  low_equiv_stkelt o (ARet a1 b) (ARet a2 b).
Hint Constructors low_equiv_stkelt : core.

Global Instance low_stkelt (o: Label) : @Equivalence (@StkElmt Label) (low_equiv_stkelt o).
Proof.
  constructor.
  (* reflexive *) intro x. destruct x; auto.
  (* symmetric *) intros x y Hxy. inv Hxy ; constructor ; symmetry; auto.
  (* transitive *) intros x y z Hxy Hyz.
  inv Hxy; inv Hyz; constructor; etransitivity; eauto.
Qed.

Hint Extern 1 =>
  match goal with
    | |- low_equiv_stkelt _ _ _ => reflexivity
  end : core.

Inductive low_equiv_list (A: Type) (low_equiv_a: A -> A -> Prop) :
  list A -> list A -> Prop :=
| le_nil: low_equiv_list low_equiv_a nil nil
| le_cons: forall a1 a2 l1 l2,
  (low_equiv_a a1 a2) ->
  (low_equiv_list low_equiv_a l1 l2) ->
  low_equiv_list low_equiv_a (a1::l1) (a2::l2).
Hint Constructors low_equiv_list : core.

Lemma low_equiv_list_app_left (A: Type) (low_equiv_a: A -> A -> Prop) :
  forall l1 l1' l2 l2',
    low_equiv_list low_equiv_a (l1++l2) (l1'++l2') ->
    length l1 = length l1' ->
    low_equiv_list low_equiv_a l1 l1'.
Proof.
  induction l1; intros; simpl in *.
  destruct l1'; [ eauto | inv H0].
  destruct l1'; [inv H0 | eauto].
  simpl in *; inv H; auto.
  constructor ; eauto.
Qed.

Lemma low_equiv_list_app_right (A: Type) (low_equiv_a: A -> A -> Prop) :
  forall l1 l1' l2 l2',
    low_equiv_list low_equiv_a (l1++l2) (l1'++l2') ->
    length l1 = length l1' ->
    low_equiv_list low_equiv_a l2 l2'.
Proof.
  induction l1; intros; simpl in *.
  destruct l1' ; [simpl in * ; auto | inv H0].
  destruct l1'; [ inv H0 | simpl in * ].
  inv H; auto.
  eapply IHl1 ; eauto.
Qed.

Lemma low_equiv_list_app (A: Type) (R: A -> A -> Prop) : forall l1 l2 l1' l2',
  low_equiv_list R l1 l2 ->
  low_equiv_list R l1' l2' ->
  low_equiv_list R (l1++l1') (l2++l2').
Proof.
  induction l1; intros.
  inv H.  simpl ; auto.
  inv H. simpl. constructor ; auto.
Qed.
(*
Lemma join_low_equiv_list (f: Z -> Z -> Z):
  forall o s1 s2 v1 v2 v1' v2' v1l v1'l v2l v2'l,
  low_equiv_list (low_equiv_stkelt o) s1 s2 ->
  low_equiv_atom o (v1, v1l) (v2, v2l) ->
  low_equiv_atom o (v1', v1'l) (v2', v2'l) ->
  low_equiv_list (low_equiv_stkelt o)
  ((AData (f v1 v1', join v1l v1'l)) :: s1)
  ((AData (f v2 v2', join v2l v2'l)) :: s2).
Proof.
  intros. constructor ; auto.
  inv H0; inv H1; constructor; auto with lat.
Qed.
*)
Lemma index_list_low_eq (A: Type) (low_equiv: A -> A -> Prop) :
  forall n l1 l2 v1 v2,
    low_equiv_list low_equiv l1 l2 ->
    index_list n l1 = Some v1 ->
    index_list n l2 = Some v2 ->
    low_equiv v1 v2.
Proof.
  induction n ; intros.
  inv H; (simpl in * ; congruence).
  destruct l1, l2; (simpl in * ; try congruence).
  inv H.
  eapply IHn ; eauto.
Qed.


Lemma index_list_Z_low_eq (A: Type) (low_equiv: A -> A -> Prop) :
  forall i l1 l2 v1 v2,
    low_equiv_list low_equiv l1 l2 ->
    index_list_Z i l1 = Some v1 ->
    index_list_Z i l2 = Some v2 ->
    low_equiv v1 v2.
Proof.
  intros. eapply index_list_low_eq; eauto.
  eapply index_list_Z_nat; eauto.
  eapply index_list_Z_nat; eauto.
Qed.

Lemma update_list_high: forall o m1 m2,
  low_equiv_list (low_equiv_atom o) m1 m2 ->
  forall a m1' o1 v l1 l2
    (Hl1 : l1 <: o = false)
    (Hl2 : l2 <: o = false),
    index_list a m1 = Some (o1, l1) ->
    update_list a (v, l2) m1 = Some m1' ->
    low_equiv_list (low_equiv_atom o) m1' m2.
Proof.
  induction 1; intros.
  destruct a; simpl in *; allinv.

  destruct a; simpl in *; allinv.
  constructor ; auto. inv H ; auto.

  case_eq (update_list a (v, l3) l1) ; intros;
  rewrite H3 in *; allinv.
  constructor; auto.
  eapply (IHlow_equiv_list a l o1 v l0) ; eauto.
Qed.

Lemma update_list_Z_high: forall o m1 m2,
  low_equiv_list (low_equiv_atom o) m1 m2 ->
  forall a m1' o1 v l1 l2
    (Hl1 : l1 <: o = false)
    (Hl2 : l2 <: o = false),
    index_list_Z a m1 = Some (o1, l1) ->
    update_list_Z a (v, l2) m1 = Some m1' ->
    low_equiv_list (low_equiv_atom o) m1' m2.
Proof.
  intros.
  eapply update_list_high with (l1 := l1) (l2 := l2); eauto.
  eapply index_list_Z_nat; eauto.
  eapply update_list_Z_nat; eauto.
Qed.


Global Instance low_list
          (A: Type)
          (R: relation A)
          (EqR: Equivalence R) : @Equivalence (list A) (@low_equiv_list A R).
Proof.
  constructor.
  (* reflexive *) unfold Reflexive. induction x; intros; constructor; auto. reflexivity.
  (* symmetric *)
  unfold Symmetric.
  induction x ; intros; (inv H ; constructor ; auto). symmetry; auto.
  (* transitive *)
  unfold Transitive.
  induction x; intros.
  inv H. auto. inv H. inv H0.
  constructor. etransitivity; eauto.
  eapply IHx ; eauto.
Qed.

Hint Extern 1 =>
  match goal with
    | |- low_equiv_list _ _ _ => reflexivity
  end : core.

Lemma update_list_low_equiv: forall a obs l  m m' o v
  (Hl : l <: obs = false),
  index_list a m = Some (o, l) ->
  update_list a (v, l) m = Some m' ->
  low_equiv_list (low_equiv_atom obs) m m'.
Proof.
  induction a; intros.
  destruct m ; simpl in *; allinv.
  constructor; auto.

  destruct m ; simpl in *; allinv.
  case_eq (update_list a (v, l) m) ; intros; rewrite H1 in *; allinv.
  constructor; eauto.
Qed.

Lemma update_list_Z_low_equiv: forall a obs l  m m' o v
  (Hl : l <: obs = false),
  index_list_Z a m = Some (o, l) ->
  update_list_Z a (v, l) m = Some m' ->
  low_equiv_list (low_equiv_atom obs) m m'.
Proof.
  intros. eapply update_list_low_equiv; eauto.
  eapply index_list_Z_nat; eauto.
  eapply update_list_Z_nat; eauto.
Qed.

Lemma update_list_low : forall o n m1 m2 a1 a2 m1' m2',
  low_equiv_list (low_equiv_atom o) m1 m2 ->
  low_equiv_atom o a1 a2 ->
  update_list n a1 m1 = Some m1' ->
  update_list n a2 m2 = Some m2' ->
  low_equiv_list (low_equiv_atom o) m1' m2'.
Proof.
  induction n ; intros.
  inv H; simpl in *; allinv.
  constructor ; auto.

  inv H.
  simpl in *; allinv.
  simpl in H2, H1.
  case_eq (update_list n a2 l2) ; case_eq (update_list n a1 l1) ; intros;
    rewrite H in * ; rewrite H5 in * ; allinv.
  constructor ; eauto.
Qed.

Lemma update_list_Z_low : forall o n m1 m2 a1 a2 m1' m2',
  low_equiv_list (low_equiv_atom o) m1 m2 ->
  low_equiv_atom o a1 a2 ->
  update_list_Z n a1 m1 = Some m1' ->
  update_list_Z n a2 m2 = Some m2' ->
  low_equiv_list (low_equiv_atom o) m1' m2'.
Proof.
  intros. eapply update_list_low; eauto.
  eapply update_list_Z_nat; eauto.
  eapply update_list_Z_nat; eauto.
Qed.

Lemma low_equiv_list_update_Z: forall o a1 a2 a1l a2l o1 o1l o2 o2l m1 m2 m1' m2' v1 v1l v2 v2l,
    low_equiv_atom o (a1, a1l) (a2, a2l) ->
    low_equiv_list (low_equiv_atom o) m1 m2 ->
    index_list_Z a1 m1 = Some (o1, o1l) ->
    index_list_Z a2 m2 = Some (o2, o2l) ->
     a1l <: o1l = true ->
     a2l <: o2l = true ->
    low_equiv_atom o (v1, v1l) (v2, v2l) ->
    update_list_Z a1 (v1, join a1l v1l) m1 = Some m1' ->
    update_list_Z a2 (v2, join a2l v2l) m2 = Some m2' ->
    low_equiv_list (low_equiv_atom o) m1' m2'.
Proof.
  intros.
  inv H; inv H5.

  eapply (@update_list_Z_low o) ; eauto.

  eapply update_list_Z_low with (3:= H6) (4:= H7) ; eauto.
  econstructor 2; eauto with lat.

  assert (low_equiv_list (low_equiv_atom o) m1' m1).
  assert (a1l \_/ v2l <: o = false) by eauto with lat.
  eapply update_list_Z_high with (4:= H1); eauto.
  destruct (flows o1l o) eqn:?; auto.
  assert (flows a1l o = true); eauto with lat.

  assert (low_equiv_list (low_equiv_atom o) m1' m2) by (etransitivity; eauto).
  assert (a2l \_/ v2l <: o = false) by eauto with lat.
  exploit (@update_list_Z_spec Atom (v2, a1l \_/ v2l)) ; eauto. intros HH.
  assert (low_equiv_list (low_equiv_atom o) m2' m2).
  eapply update_list_Z_high with (4:= H2); eauto.
  destruct (flows o2l o) eqn:?; auto.
  assert (flows a2l o = true); eauto with lat.
  etransitivity; eauto. symmetry; auto.

  assert (a1l \_/ v1l <: o = false) by eauto with lat.
  assert (low_equiv_list (low_equiv_atom o) m1' m1).
  eapply update_list_Z_high with (4:= H1); eauto.
  destruct (flows o1l o) eqn:?; auto.
  assert (flows a1l o = true); eauto with lat.

  exploit (@update_list_Z_spec Atom (v1, a1l \_/ v1l)) ; eauto. intros HH.
  assert (low_equiv_list (low_equiv_atom o) m1' m2).
  etransitivity ; eauto.

  assert (a2l \_/ v2l <: o = false) by eauto with lat.
  assert (low_equiv_list (low_equiv_atom o) m2' m2).
  eapply update_list_Z_high with (4:= H2); eauto.
  destruct (flows o2l o) eqn:?; auto.
  assert (flows a2l o = true); eauto with lat.
  etransitivity; eauto. symmetry; eauto.
Qed.

Lemma update_high_low_equiv: forall o addr m v l l' v' m',
  index_list addr m = Some (v,l) ->
  l <: o = false ->
  l <: l' = true ->
  update_list addr (v',l') m = Some m' ->
  low_equiv_list (low_equiv_atom o) m m'.
Proof.
  induction addr; intros.
  destruct m ; simpl in *; allinv.
  constructor ; eauto.
  constructor 2; auto with lat.
  destruct (flows l' o) eqn:?; auto.
  assert (flows l o = true); eauto with lat.

  destruct m ; simpl in *; allinv.
  remember (update_list addr (v', l') m) as up.
  destruct up; allinv.
  constructor; eauto.
Qed.

Lemma update_Z_high_low_equiv: forall o addr m v l l' v' m',
  index_list_Z addr m = Some (v,l) ->
  l <: o = false ->
  l <: l' = true ->
  update_list_Z addr (v',l') m = Some m' ->
  low_equiv_list (low_equiv_atom o) m m'.
Proof.
  intros. eapply update_high_low_equiv; eauto.
  eapply index_list_Z_nat; eauto.
  eapply update_list_Z_nat; eauto.
Qed.

Fixpoint below_lret (o: Label) (stk: list (@StkElmt Label)) : list StkElmt :=
  match stk with
    | nil => nil
    | (ARet (_,l) _)::stk' =>
      match flows l o with
        | true => stk
        | false => below_lret o stk'
      end
    | _::stk' => below_lret o stk'
  end.

Lemma below_lret_low_equiv : forall o l1 l2,
  low_equiv_list (low_equiv_stkelt o) l1 l2 ->
  low_equiv_list (low_equiv_stkelt o) (below_lret o l1) (below_lret o l2).
Proof.
  induction 1; intros.
  simpl ; auto.
  inv H; (simpl; auto).
  inv LEa; (rewrite H in *; auto).
  rewrite H1 ; auto.
Qed.

Lemma below_lret_adata : forall o l l',
  (forall d, In d l -> exists a : Atom, d = AData a) ->
  below_lret o (l ++ l') = below_lret o l'.
Proof.
  induction l; intros.
  simpl; auto.
  destruct a. simpl ; auto. eapply IHl ; eauto.
  intros. eapply H ; eauto. constructor 2 ; auto.

  eelim (H (ARet a b)); intros.
  congruence.
  constructor ; auto.
Qed.

Inductive low_equiv_full_state (o: Label) : @AS Label -> @AS Label -> Prop :=
| low_equiv_high:
  forall l1 l2 m1 m2 i stk1 stk2 pcv1 pcv2
    (Flowl1: l1 <: o = false)
    (Flowl2: l2 <: o = false)
    (LEm : low_equiv_list (low_equiv_atom o) m1 m2)
    (LEsH : low_equiv_list (low_equiv_stkelt o) (below_lret o stk1) (below_lret o stk2)),
    low_equiv_full_state o
      (AState m1 i stk1 (pcv1,l1))
      (AState m2 i stk2 (pcv2,l2))
| low_equiv_low:
  forall l m1 m2 i stk1 stk2 pcv
    (Flowl: l <: o = true)
    (LEm : low_equiv_list (low_equiv_atom o) m1 m2)
    (LEs : low_equiv_list (low_equiv_stkelt o) stk1 stk2),
    low_equiv_full_state o
      (AState m1 i stk1 (pcv,l))
      (AState m2 i stk2 (pcv,l)).
Hint Constructors low_equiv_full_state : core.

Global Instance low_state (o: Label) : @Equivalence AS (@low_equiv_full_state o).
Proof.
  constructor.
  (* reflexive *) intros x. destruct x. destruct apc.
  destruct (flows l o) eqn:?.
  constructor 2 ; eauto.
  constructor ; eauto.
  (* symmetry *)
  intros s s' Hss'.  inv Hss'.
  (constructor; eauto); symmetry ; eauto.
  (constructor 2; eauto) ; symmetry; eauto.
  (* transitive *)
  intros s s' s'' Hss' Hs's''.
  inv Hss' ; inv Hs's''.
  (constructor ; eauto); etransitivity; eauto.
  (constructor ; eauto); etransitivity; eauto.
  apply below_lret_low_equiv; auto.
  (constructor ; eauto); etransitivity; eauto.
  apply below_lret_low_equiv in LEs; auto.
  etransitivity; eauto.
  (constructor 2 ; eauto); etransitivity; eauto.
Qed.

Hint Extern 1 =>
  match goal with
    | |- low_equiv_full_state _ _ _ => reflexivity
  end : core.

Lemma pc_labels1 : forall o s1 s2,
  low_equiv_full_state o s1 s2 ->
  low_pc o s1 ->
  low_pc o s2.
Proof.
  induction 1; intros. unfold low_pc in *;  simpl in *.
  inv H. congruence.
  unfold low_pc in *;  simpl in *. auto.
Qed.

Lemma pc_labels2 : forall o s1 s2,
  low_equiv_full_state o s1 s2 ->
  low_pc o s2 ->
  low_pc o s1.
Proof.
  induction 1; intros. unfold low_pc in *;  simpl in *.
  inv H. congruence.
  unfold low_pc in *;  simpl in *. auto.
Qed.

Lemma index_list_low_equiv_some: forall (A: Type) (R: relation A) n e l l',
  low_equiv_list R l l' ->
  index_list n l = None ->
  index_list n l' = Some e ->
  False.
Proof.
  induction n ; intros.
  destruct l' ; inv H ; simpl in *; try congruence.
  destruct l' ; inv H ; simpl in * ; try congruence.
  eapply IHn ; eauto.
Qed.

Lemma index_list_Z_low_equiv_some: forall (A: Type) (R: relation A) n e l l',
  low_equiv_list R l l' ->
  index_list_Z n l = None ->
  index_list_Z n l' = Some e ->
  False.
Proof.
  unfold index_list_Z. intros.
  destruct (n <? 0)%Z. congruence.
  eapply index_list_low_equiv_some; eauto.
Qed.

(** Visible event for a given observer [o] *)
Inductive visible_event (o : Label) : (@Event Label) -> Prop :=
| ve_low : forall i l, l <: o = true -> visible_event o (EInt (i, l)).
Hint Constructors visible_event : core.

Lemma visible_event_dec : forall o e, {visible_event o e} + {~ visible_event o e}.
Proof.
  intros o [[x l]].
  destruct (l <: o) eqn: Hl; auto.
  right. intros H. inv H. congruence.
Defined.

End ObsEquiv.

Hint Resolve low_state : core.

Hint Constructors
  low_equiv_atom
  low_equiv_stkelt
  low_equiv_list
  low_equiv_full_state : core.

Hint Extern 1 =>
  match goal with
    | |- low_equiv_atom _ _ _ => reflexivity
    | |- low_equiv_stkelt _ _ _ => reflexivity
    | |- low_equiv_list _ _ _ => reflexivity
    | |- low_equiv_full_state _ _ _ => reflexivity
  end : core.

(** * Non-interference property *)

(** Instantiating the generic lockstep non-interference property for
    our particular abstract machine *)

Section ParamMachine.

Context {observer: Type}
        {Latt: JoinSemiLattice observer}.

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

Inductive abstract_i_equiv (o : observer) : relation (init_data abstract_machine) :=
  | ai_equiv : forall p d1 d2 n b
                      (STK : low_equiv_list (low_equiv_atom o) d1 d2),
                 abstract_i_equiv o (p,d1,n,b) (p,d2,n,b).

Global Program Instance AMObservation : TINI.Observation abstract_machine := {
  e_low := visible_event;
  e_low_dec := visible_event_dec;
  i_equiv := abstract_i_equiv
}.

Lemma low_equiv_step_pop_to_return: forall o  stk1 stk2,
  low_equiv_list (low_equiv_stkelt o) stk1 stk2 ->
  forall  rstk1 rstk2 ,
    pop_to_return stk1 rstk1 ->
    pop_to_return stk2 rstk2 ->
    low_equiv_list (low_equiv_stkelt o) rstk1 rstk2.
Proof.
  induction 1; intros.
  - invh @pop_to_return.
  - invh @pop_to_return.
    + invh @pop_to_return; eauto.
      invh low_equiv_stkelt.
    + invh (pop_to_return (a1::l1)); eauto.
      invh low_equiv_stkelt.
Qed.

Section fix_observer.
Variable o : observer.
Notation "'<<' m i s pc '>>'" := (AState m i s pc).
Notation "m1 '~~m' m2" := (low_equiv_list (low_equiv_atom o) m1 m2) (at level 20).
Notation "s1 '~~l' s2" := (low_equiv_list (low_equiv_stkelt o) s1 s2) (at level 20).
Notation "a1 '~~a' a2" := (low_equiv_atom o a1 a2) (at level 20).

Arguments low_pc {Label Latt} o s /.

Local Ltac go :=
  try congruence;
  try lia;
  auto using below_lret_low_equiv with lat;
  try apply below_lret_low_equiv;
  [> once (constructor; go) ..].

Local Ltac inv_equiv_atom :=
 match goal with
   | h: (_,_) ~~a (_,_) |- _ => inv h; simpl in *
  end.

Lemma lowstep : forall as1 e as1' as2 e' as2',
  low_equiv_full_state o as1 as2 ->
  low_pc o as1  ->
  a_step as1 e as1' ->
  a_step as2 e' as2' ->
  low_equiv_full_state o as1' as2'.
Proof.
  intros as1 e as1' as2 e' as2' He Hpc Hs1 Hs2.
  inv He. inv Hpc; congruence.

  (*destruct (a_step_instr Hs1) as [instr Hinstr].*)

  (inv Hs1 ; try congruence);
    (inv Hs2 ; try congruence); exploit_low;
  try (repeat inv_equiv_atom; go).

  Case "Push".
    assert (cv = cv0) by congruence; subst cv.
    go.

  Case "Load".
    inv_equiv_atom; try go.
    SCase "Load from low addresses".
    assert (Hmemv: low_equiv_atom o (xv, xl) (xv0, xl0)) by
        (eapply index_list_Z_low_eq with (1 := LEm)  ; eauto).
    inv Hmemv; go.

  Case "Store".
    repeat inv_equiv_atom;
    assert (m' ~~m m'0)
      by (eapply low_equiv_list_update_Z with (8:= STORE) (9:= STORE0);
          eauto with lat);
    go.

  Case "BranchNZ".
    assert (offv = offv0) by congruence; subst offv.
    inv_equiv_atom; go.

  Case "Call".
    assert (length args = length args0) by congruence.
    assert (r0 = r) by congruence; subst r0.
    exploit low_equiv_list_app_left ; eauto; intros Hl.
    exploit low_equiv_list_app_right ; eauto; intros Hr.
    inv_equiv_atom.
    SCase "Low Call".
       constructor 2; eauto with lat.
       eapply low_equiv_list_app ; eauto.

    SCase "High Call".
       constructor; auto with lat.
       rewrite below_lret_adata ; eauto.
       rewrite below_lret_adata ; eauto.
       simpl; rewrite Flowl; go.

  Case "Ret".
    spec_pop_return.
    spec_pop_return.
    exploit low_equiv_step_pop_to_return; eauto; intros HspecRet.
    inv HspecRet.
    exploit_low.
    inv_equiv_atom; go.

  Case "VRet".
    spec_pop_return.
    spec_pop_return.
    exploit low_equiv_step_pop_to_return; eauto; intros HspecRet.
    exploit_low.
    repeat inv_equiv_atom; go.
Qed.

Lemma highstep : forall as1 e as1',
  ~low_pc o as1 ->
  a_step as1 e as1' ->
  ~low_pc o as1' ->
  low_equiv_full_state o as1 as1'.
Proof.
  intros as1 e as1' Hpc Hs Hpc'.
  destruct as1. destruct apc as [ z t ]. simpl in *.
  assert (t <: o = false) by (destruct (flows t o); congruence).
  clear Hpc. inv Hs; try go.

  Case "Store".
    destruct (flows ml o) eqn:?.
    SCase "ml <: o = true".
      assert (t <: o = true) by eauto with lat.
      congruence.
    SCase "ml <: o = false".
      assert (m' ~~m amem) by
        (eapply update_list_Z_high with (4:= LOAD) (5:= STORE); eauto with lat).
      constructor ; eauto. symmetry ; auto.

  Case "Call".
    constructor; eauto with lat.
    simpl.
    erewrite below_lret_adata; [idtac|eauto].
    erewrite below_lret_adata; [idtac|eauto].
    simpl in *.
    destruct (t<:o) eqn:Hc; go.

  Case "Ret".
    spec_pop_return.
    simpl in *.
    exploit @pop_to_return_spec2; eauto. intros HTEMP. inv HTEMP.
    exploit @pop_to_return_spec3; eauto. intros HTEMP. inv HTEMP.
    destruct (flows pcl' o) eqn:e; try congruence.
    constructor ; eauto.
    rewrite below_lret_adata; eauto.
    simpl. rewrite e.
    auto.

 Case "VRet".
    spec_pop_return.
    exploit @pop_to_return_spec2; eauto. intros HTEMP. inv HTEMP.
    exploit @pop_to_return_spec3; eauto. intros HTEMP. inv HTEMP.
    simpl in *.
    destruct (flows pcl' o) eqn:e; try congruence.
    constructor ; eauto.
    simpl.
    rewrite below_lret_adata; eauto.
    simpl. rewrite e.
    auto.
Qed.

Lemma highlowstep : forall as1 e as1' as2 e' as2',
  low_equiv_full_state o as1 as2 ->
  ~low_pc o as1 ->
  a_step as1 e as1' ->
  low_pc o as1' ->
  a_step as2 e' as2' ->
  low_pc o as2' ->
  low_equiv_full_state o as1' as2'.
Proof.
  intros as1 e as1' as2 e' as2' Heq Hpc Hs1 Hpc' Hs2 Hpc''.
  inv Heq; [clear Hpc | elim Hpc; simpl ; auto].

  exploit a_step_instr; eauto. intros [instr1 Hinstr1].

  (* instr1 is Ret or VRet *)
  inv Hs1; simpl in *;
  try assert (l1 <: o = true) by (eapply join_2_rev; eassumption);
  try congruence;
  inv Hs2; simpl in *;
  try assert (l2 <: o = true) by (eapply join_2_rev; eassumption);
  try congruence.

  Case "P1 is Ret and P2 is Ret".
    spec_pop_return.
    spec_pop_return.
    revert POP0.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP.
    intros POP0.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP0.
    rewrite below_lret_adata in LEsH; eauto.
    rewrite below_lret_adata in LEsH; eauto.
    revert LEsH; simpl.
    rewrite Hpc'; rewrite Hpc''.
    intros Temp; inv Temp.
    exploit_low.
    inv_equiv_atom; go.

  Case "P1 is Ret and P2 is Vret". (* contradiction *)
    spec_pop_return.
    spec_pop_return.
    revert POP0.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP; intros POP0.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP0.
    rewrite below_lret_adata in LEsH; eauto.
    rewrite below_lret_adata in LEsH; eauto.
    revert LEsH; simpl.
    rewrite Hpc'; rewrite Hpc''.
    intros Temp; inv Temp.
    exploit_low.

  Case "P1 is VRet and P2 is Ret". (* contradiction *)
    spec_pop_return.
    spec_pop_return.
    revert POP0.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP; intros POP0.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP0.
    rewrite below_lret_adata in LEsH; eauto.
    rewrite below_lret_adata in LEsH; eauto.
    revert LEsH; simpl.
    rewrite Hpc'; rewrite Hpc''.
    intros Temp; inv Temp.
    exploit_low.

  Case "P1 is Vret and P2 is Vret".
    spec_pop_return.
    spec_pop_return.
    revert POP0.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP; intros POP0.
    exploit @pop_to_return_spec2; eauto; intros Temp; inv Temp.
    exploit @pop_to_return_spec3; eauto; intros Temp; inv Temp.
    clear POP0.
    rewrite below_lret_adata in LEsH; eauto.
    rewrite below_lret_adata in LEsH; eauto.
    revert LEsH; simpl.
    rewrite Hpc'; rewrite Hpc''.
    intros Temp; inv Temp.
    exploit_low.
    inv_equiv_atom; go.
Qed.

End fix_observer.

Lemma low_equiv_list_map : forall E1 E2
                                  (R1: relation E1)
                                  (R2: relation E2)
                                  g f (l1 l2: list E1),
                             (forall x y, R1 x y -> R2 (f x) (g y)) ->
                             low_equiv_list R1 l1 l2 ->
                             low_equiv_list R2 (map f l1) (map g l2).
Proof.
  induction 2; intros; simpl; auto.
Qed.

Lemma below_lret_alldata :
  forall o l,
    (forall e, In e l -> exists a, e = AData a) ->
    (below_lret o l) = nil.
Proof.
  induction l ; intros.
  auto.
  destruct a ; simpl. eapply IHl ; eauto.
  intros ; eapply H ; eauto. constructor 2; auto.
  eelim (H (ARet a b)) ; eauto.
  congruence. constructor; auto.
Qed.

Lemma map_AData :
  forall T (l: list (@Atom T)) e,
   In e (map (fun a : Atom => AData a) l) -> exists a : Atom, e = AData a.
Proof.
  induction l ; intros; inv H; eauto.
Qed.

Program Instance AMUnwindingSemantics :
  TINI.UnwindingSemantics AMObservation := {
  s_equiv := low_equiv_full_state;
  s_low := low_pc;
  s_low_dec := low_pc_dec
}.

Next Obligation.
  inv H.
  destruct (flows o0 o) eqn:E.
  constructor 2; eauto.
  eapply low_equiv_list_map; eauto.
  constructor ; eauto.
  rewrite below_lret_alldata; eauto.
  rewrite below_lret_alldata; eauto.
  apply map_AData.
  apply map_AData.
Qed.

Next Obligation.
  intros x y H. rewrite <- H. reflexivity.
Qed.

Next Obligation.
  inv H; split; intros H; inv H; try congruence;
  unfold low_pc; simpl; trivial.
Qed.

Next Obligation.
  unfold low_pc.
  inv H; simpl;
  try match goal with
        | H : visible_event _ _ |- _ =>
          inv H
      end.
  eauto with lat.
Qed.

Next Obligation.
  inv H1; inv H2;
  try solve [[> once (econstructor ; intros H'; inv H'; solve [eauto]) ..]];
  match goal with
    | H : low_equiv_full_state _ _ _ |- _ =>
      inv H; try congruence
  end;
  try solve [
        constructor; intros H; inv H;
        match goal with
          | H1 : ?pcl <: ?o = false,
            H2 : ?l \_/ ?pcl <: ?o = true |- _ =>
            apply join_2_rev in H2; congruence
        end
      ];
  try solve [exploit @index_list_Z_low_eq_instr; eauto; intros H; inv H].
  exploit_low.
  inv LEa; try reflexivity.
  constructor; intros H; inv H;
  match goal with
    | H : ?l \_/ ?pcl <: ?o = true |- _ =>
      apply join_1_rev in H; congruence
  end.
Qed.

Next Obligation.
  eapply lowstep; eauto.
Qed.

Next Obligation.
  rewrite <- H0.
  symmetry.
  eapply highstep; eauto.
Qed.

Next Obligation.
  eapply highlowstep; eauto.
Qed.

Theorem abstract_noninterference_short :
  TINI.tini AMObservation.
Proof.
  apply TINI.noninterference.
  exact AMUnwindingSemantics.
Qed.

Theorem abstract_noninterference :
  @TINI.tini abstract_machine AMObservation.
Proof.
  apply TINI.noninterference.
  exact AMUnwindingSemantics.
Qed.

End ParamMachine.
