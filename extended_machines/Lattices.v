Require Import EquivDec.
Require Export RelationClasses.
Require Export SetoidClass.
Require Import ZArith.
Require Import ListSet.
Require Import List.
Require Import Bool.
Require Import Eqdep_dec.

Require Export Utils.

Open Scope bool_scope.

(** Assumptions: labels form a join-semi-lattice. *)

(** * Definition *)

Class JoinSemiLattice (Lab: Type) :=
{ bot : Lab
; join : Lab -> Lab -> Lab
; flows : Lab -> Lab -> bool
; bot_flows : forall l, flows bot l  = true
; flows_refl : forall l, flows l l  = true
; flows_trans : forall l1 l2 l3,  flows l1 l2  = true -> flows l2 l3  = true -> flows l1 l3  = true
; flows_antisymm : forall l1 l2,  flows l1 l2  = true -> flows l2 l1 = true -> l1 = l2
; flows_join_right : forall l1 l2, flows l1 (join l1 l2) = true
; flows_join_left : forall l1 l2, flows l2 (join l1 l2) = true
; join_minimal : forall l1 l2 l, flows l1 l  = true -> flows l2 l  = true -> flows (join l1 l2) l = true
}.

Notation "l1 \_/ l2" := (join l1 l2) (at level 40) : type_scope.
Notation "l1 <: l2" := (flows l1 l2) (at level 50, no associativity) : type_scope.

(* Might be used at some point as the default for clearance
Parameter top : Lab.
Hypothesis flows_top : forall l, l <: top. *)

Hint Resolve
  @flows_refl
  @flows_trans
  @flows_join_left
  @flows_join_right
  @flows_antisymm
  @join_minimal: lat.

(** Immediate properties from the semi-lattice structure. *)
Section JoinSemiLattice_properties.

Context {T: Type}.

(* AAA: used to be assumption, not used *)
Lemma flows_join {L:JoinSemiLattice T} : forall l1 l2, l1 <: l2 = true <-> l1 \_/ l2 = l2.
Proof.
  intros.
  split.
  - intros H.
    apply flows_antisymm.
    + apply join_minimal; auto with lat.
    + apply flows_join_left.
  - intros H.
    rewrite <- H.
    auto with lat.
Qed.

Lemma join_1_rev {L: JoinSemiLattice T} : forall l1 l2 l,
  l1 \_/ l2 <: l = true -> l1 <: l = true.
Proof. eauto with lat. Qed.

Lemma join_2_rev {L: JoinSemiLattice T} : forall l1 l2 l,
  l1 \_/ l2 <: l  = true -> l2 <: l  = true.
Proof. eauto with lat. Qed.

Lemma join_1 {L: JoinSemiLattice T} : forall l l1 l2,
  l <: l1  = true -> l <: l1 \_/ l2  = true.
Proof. eauto with lat. Qed.

Lemma join_2 {L: JoinSemiLattice T}: forall l l1 l2,
  l <: l2 = true -> l <: l1 \_/ l2 = true.
Proof. eauto with lat. Qed.

Lemma join_bot_right {L: JoinSemiLattice T} : forall l,
  l \_/ bot = l.
Proof.
  eauto using bot_flows with lat.
Qed.

Lemma join_bot_left {L: JoinSemiLattice T} : forall l,
  bot \_/ l = l.
Proof. eauto using bot_flows with lat.
Qed.

Lemma not_flows_not_join_flows_left {L: JoinSemiLattice T}: forall l l1 l2,
  l1 <: l = false ->
  (l1 \_/ l2) <: l = false.
Proof.
  intros.
  destruct (flows (l1 \_/ l2) l) eqn:E.
  exploit join_1_rev; eauto.
  auto.
Qed.

Lemma not_flows_not_join_flows_right {L: JoinSemiLattice T}: forall l l1 l2,
  l2 <: l = false ->
  (l1 \_/ l2) <: l = false.
Proof.
  intros.
  destruct (flows (l1 \_/ l2) l) eqn:E.
  exploit join_2_rev; eauto.
  auto.
Qed.

Lemma join_assoc {L:JoinSemiLattice T} : forall l1 l2 l3, l1 \_/ (l2 \_/ l3) = (l1 \_/ l2) \_/ l3.
Proof.
  intros.
  apply flows_antisymm.
  - repeat apply join_minimal; eauto using join_1, join_2, flows_refl.
  - repeat apply join_minimal; eauto using join_1, join_2, flows_refl.
Qed.

Lemma join_comm {L:JoinSemiLattice T} : forall l1 l2, l1 \_/ l2 = l2 \_/ l1.
Proof.
  intros. apply flows_antisymm; eauto with lat.
Qed.

Lemma join_refl {L:JoinSemiLattice T} : forall l, l \_/ l = l.
Proof.
  intros.
  apply flows_antisymm; eauto with lat.
Qed.

End JoinSemiLattice_properties.

Hint Resolve
  @join_1
  @join_2
  @bot_flows
  @not_flows_not_join_flows_right
  @not_flows_not_join_flows_left : lat.

(** The two point lattice *)
Inductive Lab : Set :=
  | L : Lab
  | H : Lab.

Instance HL : JoinSemiLattice Lab :=
{  bot := L
;  join l1 l2 :=
     match l1, l2 with
       | H, _ => H
       | _, H => H
       | L, L => L
     end
; flows l1 l2 :=
    match l1, l2 with
      | L, _ => true
      | _, H => true
      | _, _ => false
    end
}.
Proof.
auto.
intros l; destruct l; auto.
intros l1 l2 l3; destruct l1, l2, l3; auto.
intros l1 l2; destruct l1, l2; auto.
intuition.
intuition.
intros l1 l2; destruct l1, l2; auto.
intros l1 l2; destruct l1, l2; auto.
intros l1 l2 l; destruct l1, l2, l; auto.
Defined.

Instance LatEqDec (T : Type) {Lat : JoinSemiLattice T} : EqDec T eq.
  intros x y.
  destruct (x <: y) eqn:xy;
  destruct (y <: x) eqn:yx; try (right; congruence).
  - left. compute. eauto with lat.
  - generalize (flows_refl x). intros.
    right. congruence.
Defined.

Module Type ZFSET.

  Parameter t : Type.
  Parameter elements : t -> list Z.
  Definition In (z:Z) (s:t) := In z (elements s).

  Parameter empty : t.
  Parameter elements_empty : elements empty = nil.

  Parameter add : Z -> t -> t.
  Parameter In_add : forall z s x,
     In x (add z s) <-> x=z \/ In x s.

  Parameter union : t -> t -> t.
  Parameter In_union : forall s1 s2 x,
     In x (union s1 s2) <-> In x s1 \/ In x s2.

  Parameter incl : t -> t -> bool.
  Parameter incl_spec : forall s1 s2,
    incl s1 s2 = true <-> List.incl (elements s1) (elements s2).

  Parameter antisym : forall s1 s2,
  incl s1 s2 = true ->
  incl s2 s1 = true ->
  s1 = s2.

End ZFSET.

Module Zset : ZFSET.

  Definition mem := set_mem Z.eq_dec.

  Fixpoint sorted (l:list Z) : bool :=
    match l with
      | nil => true
      | x :: q1 =>
        match q1 with
          | nil => true
          | y :: q =>
            Z.ltb x y && sorted q1
        end
    end.

  Record t_ := ZS { elements:> list Z; sorted_elements: sorted elements = true }.
  Definition t := t_.
  Hint Resolve sorted_elements.

  Definition In (z:Z) (s:t) := In z (elements s).

  Program Definition empty : t := ZS nil _.

  Definition elements_empty : elements empty = nil.
  Proof.
    simpl; auto.
  Qed.

  Lemma mem_elements : forall s z,
    mem z s = true <-> List.In z s.
  Proof.
    unfold mem; split; intros.
    - apply (set_mem_correct1 Z.eq_dec); auto.
    - apply (set_mem_correct2 Z.eq_dec); auto.
  Qed.

  Fixpoint insert (a:Z) (l:list Z) : list Z :=
    match l with
        nil => a::nil
      | x::q => if Z_lt_dec a x then a::l else
                  if Z.eq_dec a x then x::q
                  else x::(insert a q)
    end.

(* Zlt_is_lt_bool: forall n m : Z, (n < m)%Z <-> (n <? m)%Z = true *)

  Lemma sorted_insert : forall l z,
    sorted l = true -> sorted (insert z l) = true.
  Proof.
    induction l; simpl; auto; intros.
    destruct l; auto.
    - destruct Z_lt_dec; simpl.
      + rewrite (Zlt_is_lt_bool z a) in l.
        rewrite l; auto.
      + destruct Z.eq_dec; simpl; auto.
        rewrite andb_true_iff; split; auto.
        rewrite <- Zlt_is_lt_bool.
        omega.
    - rewrite andb_true_iff in H0; destruct H0.
      destruct Z_lt_dec.
      + simpl.
        rewrite Zlt_is_lt_bool in l0.
        rewrite l0; rewrite H0.
        simpl in H1; rewrite H1.
        auto.
      + destruct Z.eq_dec; simpl.
        * rewrite H0.
          simpl in H1; rewrite H1.
          auto.
        * {
            destruct Z_lt_dec; simpl.
            - rewrite Zlt_is_lt_bool in l0.
              rewrite l0.
              assert (a < z)%Z by omega.
              rewrite Zlt_is_lt_bool in H2.
              rewrite H2.
              simpl in H1; rewrite H1; auto.
            - destruct Z.eq_dec.
              + rewrite H0; auto.
              + rewrite H0.
                generalize (IHl z); simpl.
                destruct Z_lt_dec; try omega.
                destruct Z.eq_dec; try omega.
                auto.
          }
  Qed.

  Lemma In_insert : forall x l z,
     List.In x (insert z l) <-> x=z \/ List.In x l.
  Proof.
    split.
    - generalize dependent z; induction l.
      + simpl; intuition.
      + simpl; intros z.
        destruct Z_lt_dec; simpl; auto.
        * intuition.
        * destruct Z.eq_dec.
          simpl; intuition.
          simpl; intuition.
          apply IHl in H1; intuition.
    - generalize dependent z; induction l.
      + simpl; intuition.
      + intro z; simpl.
        destruct Z_lt_dec; simpl; auto.
        * intuition.
        * destruct Z.eq_dec.
          simpl; intuition.
          simpl; intuition.
  Qed.

  Program Definition add (z:Z) (s: t) : t :=
    ZS (insert z s) _.
  Next Obligation.
    destruct s; simpl.
    apply sorted_insert; auto.
  Qed.

  Lemma In_add : forall z s x,
     In x (add z s) <-> x=z \/ In x s.
  Proof.
    unfold add, In; destruct s as [l Hl]; simpl.
    intros; apply In_insert.
  Qed.

  Fixpoint union_list (l1 l2:list Z) : list Z :=
    match l1 with
      | nil => l2
      | x::q => union_list q (insert x l2)
    end.

  Lemma sorted_union : forall l1 l2,
    sorted l2 = true -> sorted (union_list l1 l2) = true.
  Proof.
    induction l1; simpl; auto.
    eauto using sorted_insert.
  Qed.

  Lemma In_union_list : forall l1 l2 x,
     List.In x (union_list l1 l2) <-> List.In x l1 \/ List.In x l2.
  Proof.
    induction l1; simpl; intuition.
    - rewrite IHl1 in H0; intuition.
      rewrite In_insert in H1; intuition.
    - rewrite IHl1.
      rewrite In_insert; intuition.
    - rewrite IHl1; auto.
    - rewrite IHl1.
      rewrite In_insert; intuition.
  Qed.

  Program Definition union (s1 s2: t) : t :=
    ZS (union_list s1 s2) _.
  Next Obligation.
    destruct s1 as [l1 H1].
    destruct s2 as [l2 H2].
    simpl.
    apply sorted_union; auto.
  Qed.

  Lemma In_union : forall s1 s2 x,
     In x (union s1 s2) <-> In x s1 \/ In x s2.
  Proof.
    unfold union, In; destruct s1; destruct s2; simpl.
    apply In_union_list.
  Qed.

  Fixpoint set_incl (l1 l2 : list Z) : bool :=
    match l1 with
      | nil => true
      | x::q => mem x l2 && set_incl q l2
    end.

  Lemma set_incl_spec : forall l1 l2,
    set_incl l1 l2 = true <-> List.incl l1 l2.
  Proof.
    unfold incl.
    induction l1; simpl; intuition.
    - rewrite andb_true_iff in H0; destruct H0; subst.
      unfold mem in *.
      apply set_mem_correct1 in H0; auto.
    - rewrite andb_true_iff in H0; destruct H0; subst.
      rewrite IHl1 in H1; auto.
    - rewrite andb_true_iff; split.
      + apply set_mem_correct2; auto.
        apply H0; auto.
      + rewrite IHl1.
        intros; auto.
  Qed.

  Definition incl (s1 s2:t) : bool :=
    let (l1, _) := s1 in
    let (l2, _) := s2 in
    set_incl l1 l2.

  Lemma incl_spec : forall s1 s2,
    incl s1 s2 = true <-> List.incl (elements s1) (elements s2).
  Proof.
    destruct s1; destruct s2; simpl.
    apply set_incl_spec.
  Qed.


  Lemma inv_sorted_cons1: forall a l,
    sorted (a :: l) = true -> sorted l = true.
  Proof.
    simpl; destruct l; auto.
    rewrite andb_true_iff; intuition.
  Qed.

  Lemma inv_sorted_cons_2_aux: forall l,
    sorted l = true ->
    match l with
      | nil => True
      | a::l =>
        forall x, List.In x l -> (a < x)%Z
    end.
  Proof.
    simpl; induction l; intuition.
    destruct l; intuition.
    simpl in H0.
    rewrite andb_true_iff in H0; intuition.
    simpl in H1; destruct H1.
    - subst.
      rewrite <- Zlt_is_lt_bool in H2; auto.
    - generalize (H0 _ H1).
      rewrite <- Zlt_is_lt_bool in H2; omega.
  Qed.

  Lemma inv_sorted_cons_2: forall a l,
    sorted (a :: l) = true ->
    forall x, List.In x l -> (a < x)%Z.
  Proof.
    destruct l; intuition.
    generalize (inv_sorted_cons_2_aux _ H0).
    auto.
  Qed.

  Lemma inv_sorted_cons_3: forall a l,
    sorted (a :: l) = true ->
    ~ List.In a l.
  Proof.
    red; intros.
    assert (a<a)%Z.
    eapply inv_sorted_cons_2; eauto.
    omega.
  Qed.

  Lemma set_antisym : forall l1 l2,
    List.incl l1 l2 ->
    List.incl l2 l1 ->
    sorted l1 = true -> sorted l2 = true ->
    l1 = l2.
  Proof.
    unfold List.incl.
    induction l1; destruct l2; intros; auto.
    - elim H1 with z; simpl; auto.
    - elim H0 with a; simpl; auto.
    - assert (a=z).
        destruct (H0 a); simpl; auto.
        destruct (H1 z); simpl; auto.
        exploit inv_sorted_cons_2; eauto.
        clear H3.
        exploit inv_sorted_cons_2; eauto.
        omega.
      subst.
      f_equal.
      apply IHl1.
      + intros x T; destruct (H0 x); simpl; auto.
        subst.
        apply inv_sorted_cons_3 in H2; intuition.
      + intros x T; destruct (H1 x); simpl; auto.
        subst.
        apply inv_sorted_cons_3 in H3; intuition.
      + eapply inv_sorted_cons1; eauto.
      + eapply inv_sorted_cons1; eauto.
  Qed.

  Lemma antisym : forall s1 s2,
    incl s1 s2 = true ->
    incl s2 s1 = true ->
    s1 = s2.
  Proof.
    destruct s1 as [l1 H1]; destruct s2 as [l2 H2]; simpl; intros.
    assert (l1=l2).
      eapply set_antisym; eauto.
      rewrite set_incl_spec in H0; auto.
      rewrite set_incl_spec in H3; auto.
    subst.
    assert (H1=H2).
    apply eq_proofs_unicity.
    destruct x; destruct y; intuition congruence.
    f_equal.
    assumption.
  Qed.

End Zset.

Lemma Zset_add_incl : forall x s, Zset.incl s (Zset.add x s) = true.
Proof.
  intros; rewrite Zset.incl_spec.
  intros a H.
  generalize (Zset.In_add x s a); unfold Zset.In.
  intro T; rewrite T; auto.
Qed.

Instance ZsetLat : JoinSemiLattice Zset.t :=
{  bot := Zset.empty
;  join := Zset.union
;  flows := Zset.incl
}.
Proof.
  - intros s; rewrite Zset.incl_spec; intros x.
    rewrite Zset.elements_empty; simpl; intuition.
  - intros s; rewrite Zset.incl_spec; intros x; auto.
  - intros s1 s2 s3; repeat rewrite Zset.incl_spec.
    unfold incl; eauto.
  - intros; eapply Zset.antisym; eauto.
  - intros s1 s2; rewrite Zset.incl_spec; intros x; auto.
    intros; apply Zset.In_union; auto.
  - intros s1 s2; rewrite Zset.incl_spec; intros x; auto.
    intros; apply Zset.In_union; auto.
  - intros s1 s2 s3; repeat rewrite Zset.incl_spec.
    unfold incl; intros.
    rewrite (Zset.In_union s1 s2 a) in H2.
    intuition.
Defined.
