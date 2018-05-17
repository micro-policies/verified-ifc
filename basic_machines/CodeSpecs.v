Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Require Import Instr.
Require Import Semantics.
Require Import Concrete.
Require Import CodeGen.
Require Import CodeTriples.
Require Import ConcreteMachine.
Require Import ConcreteExecutions.

(** Proof of various [HT], [GT], and [HTEscape] style specifications of (generic)
code generators, and concrete (privileged) code. *)

(** * Contained [HT] specifications *)

Section CodeSpecs.
Local Open Scope Z_scope.

Ltac run1 := eapply rte_step; eauto; econstructor; eauto.

Lemma nop_spec: forall Q,
  HT nop Q Q.
Proof.
  unfold nop, HT; simpl; intros.
  split_vc.
  apply_f_equal rte_refl; subst; rec_f_equal ltac:(try omega; eauto).
Qed.

Lemma add_spec: forall Q,
  HT [Add]
     (fun m s => exists s0 z1 l1 z2 l2,
                   s = (z1,l1) ::: (z2,l2) ::: s0
                   /\ Q m ((z1 + z2,handlerTag) ::: s0))
     Q.
Proof.
  unfold HT; split_vc; subst; run1.
Qed.

Lemma sub_spec: forall Q,
  HT [Sub]
     (fun m s => exists s0 z1 l1 z2 l2,
                   s = (z1,l1) ::: (z2,l2) ::: s0
                   /\ Q m ((z1 - z2,handlerTag) ::: s0))
     Q.
Proof.
  unfold HT; split_vc; subst; run1.
Qed.

Lemma push_spec : forall i Q,
  HT [Push i]
     (fun m s0 => Q m ((i,handlerTag):::s0))
     Q.
Proof.
  unfold HT; split_vc; subst; run1.
Qed.

Lemma load_spec: forall Q,
  HT [Load]
     (fun m s0 => exists a v vl s,
                    s0 = (a,handlerTag) ::: s /\
                   index_list_Z a m = Some(v,vl) /\
                   Q m ((v,vl) ::: s))
     Q.
Proof.
  unfold HT; split_vc; subst; run1.
Qed.

Lemma loadFrom_spec : forall a (Q: memory-> stack -> Prop),
  HT (loadFrom a)
     (fun m s => exists v vl, index_list_Z a m = Some (v,vl) /\ Q m ((v,vl):::s))
     Q.
Proof.
  intros.
  eapply HT_compose_bwd.
  eapply load_spec.
  eapply HT_strengthen_premise.
  eapply push_spec.
  split_vc.
Qed.

(** To prove that addresses are valid per this definition, we just
   need to know that that the memory is at least as large as the
   [tmuCacheSize], since we only use [valid_address] assumptions for
   [addrTag*]. *)
Definition valid_address a (m: memory) :=
  (0 <= a) /\ (Z.to_nat a < length m)%nat.

Lemma valid_address_upd: forall a a' vl m m',
  valid_address a m ->
  upd_m a' vl m = Some m' ->
  valid_address a m'.
Proof.
  unfold valid_address; intuition.
  unfold upd_m in *.
  destruct (a' <? 0).
  - discriminate.
  - erewrite update_preserves_length; eauto.
Qed.

Lemma valid_read: forall a m,
  valid_address a m ->
  exists v, read_m a m = Some v.
Proof.
  intros a m H.
  unfold valid_address in H.
  unfold read_m.
  destruct (a <? 0) eqn:E.
  - rewrite Z.ltb_lt in E. omega.
  - remember (Z.to_nat a) as n; clear Heqn.
    destruct H as [_ Hbound].
    generalize dependent n.
    generalize dependent m.
    induction m; intros.
    + simpl in *; omega.
    + destruct n eqn:En; subst.
      * simpl; eauto.
      * simpl in Hbound.
        apply lt_S_n in Hbound.
        eauto.
Qed.

Lemma valid_store: forall a v m,
  valid_address a m ->
  exists m', upd_m a v m = Some m'.
Proof.
  intros.
  unfold valid_address in H.
  eapply update_list_Z_Some; intuition auto.
Qed.

Lemma store_spec: forall Q a al v vl,
  forall m s,
  HT [Store]
     (fun m0 s0 => s0 = (a,al) ::: (v,vl) ::: s /\
                   upd_m a (v,vl) m0 = Some m /\
                   Q m s)
     Q.
Proof.
  unfold HT; split_vc; subst; run1.
Qed.

Lemma storeAt_spec: forall a v vl Q,
  forall m s,
  HT (storeAt a)
     (fun m0 s0 => s0 = (v,vl) ::: s /\
                   upd_m a (v,vl) m0 = Some m /\
                   Q m s)
     Q.
Proof.
  intros.
  eapply HT_compose_bwd.
  eapply store_spec.
  eapply HT_strengthen_premise.
  eapply push_spec.
  split_vc.
  subst; split_vc.
Qed.

Lemma skipNZ_continuation_spec_NZ: forall c Q v l,
  v <> 0 ->
  HT   (skipNZ (length c) ++ c)
       (fun m s => (exists s', s = CData (v,l) :: s'
                               /\ Q m s'))
       Q.
Proof.
  unfold HT; split_vc.

  (* massage to match the rule we want to run *)
  match goal with
    | |- context[n + ?z] =>
      replace (n + z) with (if v =? 0 then n + 1 else n + z)
  end.
  run1.
  rewrite <- Z.eqb_neq in H. rewrite H. auto.
Qed.

Lemma skipNZ_spec_Z: forall n Q v l,
  v = 0 ->
  HT   (skipNZ n)
       (fun m s => (exists s', s = CData (v,l) :: s'
                               /\ Q m s'))
       Q.
Proof.
  unfold HT; split_vc.

  (* pick the rule we want to run *)
  eapply rte_step; auto.
  apply_f_equal cstep_branchnz_p.
  eauto.
Qed.

Lemma skipNZ_continuation_spec_Z: forall c P Q v l,
  v = 0 ->
  HT   c P Q  ->
  HT   (skipNZ (length c) ++ c)
       (fun m s => (exists s', s = CData (v,l) :: s'
                               /\ P m s'))
       Q.
Proof.
  intros c P Q v l Hv HTc.
  eapply HT_compose.
  eapply skipNZ_spec_Z; auto.
  auto.
Qed.

Lemma skip_spec: forall c Q,
  HT   (skip (length c) ++ c)
       Q
       Q.
Proof.
  intros c P.
  unfold skip.
  rewrite app_ass.
  eapply HT_compose_bwd.
  eapply skipNZ_continuation_spec_NZ with (v:= 1); omega.
  eapply HT_strengthen_premise.
  eapply push_spec.
  split_vc.
Qed.

Lemma ifNZ_spec_Z: forall v l t f P Q,
  HT   f P Q ->
  v = 0 ->
  HT   (ifNZ t f)
       (fun m s => (exists s', s = CData (v,l) :: s' /\ P m s'))
       Q.
Proof.
  intros v l t f P Q HTf Hveq0.
  unfold ifNZ.
  rewrite app_ass.
  eapply HT_compose.
  apply skipNZ_spec_Z; auto.
  eapply HT_compose; eauto.
  apply skip_spec.
Qed.

Lemma ifNZ_spec_NZ: forall v l t f P Q,
  HT   t P Q ->
  v <> 0 ->
  HT   (ifNZ t f)
       (fun m s => (exists s', s = CData (v,l) :: s' /\ P m s'))
       Q.
Proof.
  intros v l t f P Q HTt Hveq0.
  unfold ifNZ.
  rewrite <- app_ass.
  eapply HT_compose; eauto.
  apply skipNZ_continuation_spec_NZ; auto.
Qed.

Lemma ifNZ_spec_helper: forall v l t f Pt Pf Q,
  HT   t Pt Q ->
  HT   f Pf Q ->
  HT   (ifNZ t f)
       (fun m s => ((v <> 0 -> exists s', s = CData (v,l) :: s' /\ Pt m s') /\
                    (v =  0 -> exists s', s = CData (v,l) :: s' /\ Pf m s')))
       Q.
Proof.
  intros v l t f Pt Pf Q HTt HTf.
  eapply HT_decide_join with (D := fun v => v = 0).
  apply ifNZ_spec_NZ.
  apply ifNZ_spec_Z.
  intros; omega.
  auto.
  auto.
Qed.

Lemma ifNZ_spec: forall v l t f Pt Pf Q,
  HT   t Pt Q ->
  HT   f Pf Q ->
  HT   (ifNZ t f)
       (fun m s => (exists s', s = CData (v,l) :: s' /\
                                   (v <> 0 -> Pt m s') /\
                                   (v =  0 -> Pf m s')))
       Q.
Proof.
  intros v l t f Pt Pf Q HTt HTf.
  eapply HT_strengthen_premise.
  eapply ifNZ_spec_helper; eauto.
  intros m s [s' [s_eq [HNZ HZ]]].
  destruct (dec_eq v 0); subst; intuition;
    eexists; intuition.
Qed.

(* I need to existentially bind [v] for the [ite_spec]. May have been
   easier to use existentials from the beginning ... *)
Lemma ifNZ_spec_existential: forall t f Pt Pf Q,
  HT   t Pt Q ->
  HT   f Pf Q ->
  HT   (ifNZ t f)
       (fun m s => (exists v l s', s = CData (v,l) :: s' /\
                                   (v <> 0 -> Pt m s') /\
                                   (v =  0 -> Pf m s')))
       Q.
Proof.
  intros t f Pt Pf Q HTt HTf.
  eapply HT_forall_exists.
  intro v.
  eapply HT_forall_exists.
  intro l.
  apply ifNZ_spec.
  auto.
  auto.
Qed.

(* Might make more sense to make [Qc] be the thing that [Qc] implies
   here.  I.e., this version has an implicit use of
   [HT_strengthen_premise] in it, which could always be inserted
   manually when needed. *)
Lemma ite_spec: forall c t f (P Pt Pf: HProp) Q,
  let P' := fun m s => exists v l s', s = (v,l) ::: s' /\
                                      (v <> 0 -> Pt m s') /\
                                      (v =  0 -> Pf m s') in
  HT   c P P' ->
  HT   t Pt Q ->
  HT   f Pf Q ->
  HT   (ite c t f) P Q.
Proof.
  intros c t f P Pt Pf Q P' HTc HTt HTf.
  unfold ite.
  eapply HT_compose.
  apply HTc.
  apply ifNZ_spec_existential.
  auto.
  auto.
Qed.

(** A version of [ite_spec] that restricts the effect of the condition
   code [c] to pushing one value to the stack.

   In [genApplyRule_spec] we are considering a particular memory,
   [m0], so, here it helps to make the memory a parameter. *)
Lemma ite_spec_specialized: forall v c t f Q, forall m0 s0,
  let P := fun m s => m = m0 /\ s = s0 in
  HT c P  (fun m s => m = m0 /\ s = (v,handlerTag) ::: s0) ->
  (v <> 0 -> HT t P Q) ->
  (v =  0 -> HT f P Q) ->
  HT (ite c t f) P Q.
Proof.
  intros v c t f Q m0 s0 P HTc HZ HNZ.
  eapply ite_spec with (Pt := fun m s => v <> 0 /\ m = m0 /\ s = s0)
                       (Pf := fun m s => v =  0 /\ m = m0 /\ s = s0).
  eauto.
  eapply HT_weaken_conclusion.
  eauto.

  intros m s  Heq.
  simpl in Heq.
  intuition eauto. subst.
  do 3 eexists. split; eauto.
  split; eauto.

  eapply HT_fold_constant_premise; auto.
  eapply HT_fold_constant_premise; auto.
Qed.

Lemma cases_spec_base: forall d P Q,
  HT   d P Q -> HT   (cases nil d) P Q.
Proof.
  auto.
Qed.

Lemma cases_spec_step: forall c b cbs d P (Pt Pf Q: HProp),
  let P' := fun m s => exists v l s', s = (v,l) ::: s' /\
                                      (v <> 0 -> Pt m s') /\
                                      (v =  0 -> Pf m s') in
  HT   c P P' ->
  HT   b Pt Q ->
  HT   (cases cbs d) Pf Q ->
  HT   (cases ((c,b)::cbs) d) P Q.
Proof.
  intros.
  eapply ite_spec; eauto.
Qed.

(** A specialized spec for the [cases] combinator.

   If

   - the conditions don't modify the existing stack or memory,
     but just push a value onto the stack, and that value is computed as
     a function of the stack and memory;

   - the different branches have different conclusions.

  Then if [cases] terminates, the conclusion of the first branch whose
  guard returned non-zero holds.

  Actually, that's what you get if you unfold this definition over a
  list of [(guard, branch)] pairs; this spec is just one step of
  unfolding. *)

Lemma cases_spec_step_specialized: forall c vc b cbs d P Qb Qcbs,
  (* This could be abstracted: code that transforms the stack by
  pushing one value computed from the existing stack and memory *)
  (forall m0 s0,
     HT   c (fun m s => P m0 s0 /\
                        m = m0 /\
                        s = s0)
            (fun m s => P m0 s0 /\
                        m = m0 /\
                        s = CData (vc m0 s0, handlerTag) :: s0)) ->
  HT   b P Qb ->
  HT   (cases cbs d) P Qcbs ->
  (forall m0 s0,
    HT   (cases ((c,b)::cbs) d) (fun m s => P m0 s0 /\
                                            m = m0 /\
                                            s = s0)
                                (fun m s => (vc m0 s0 <> 0 -> Qb m s) /\
                                            (vc m0 s0 = 0 -> Qcbs m s))).
Proof.
  intros c vc b cbs d P Qb Qcbs Hc Hb Hcbs.
  intros m0 s0.
  pose (Hc m0 s0) as Hcm0s0.
  eapply ite_spec with (Pt := (fun m s => P m s /\ vc m0 s0 <> 0))
                       (Pf := (fun m s => P m s /\ vc m0 s0 =  0)).
  eapply HT_weaken_conclusion.
  exact Hcm0s0.

  intuition.
  exists (vc m0 s0).
  exists handlerTag.
  exists s0.
  intuition; subst; auto.

  apply (HT_consequence' _ _ _ _ _ Hb); intuition.
  destruct H as (? & ? & ? & H).
  exfalso. eauto.

  apply (HT_consequence' _ _ _ _ _ Hcbs); intuition.
  destruct H as (? & ? & ? & H).
  exfalso. eauto.
Qed.

Lemma genTrue_spec: forall Q,
  HT genTrue
     (fun m s => Q m ((1,handlerTag):::s))
     Q.
Proof.
  eapply push_spec.
Qed.

Lemma genFalse_spec: forall Q,
  HT genFalse
     (fun m s => Q m ((0,handlerTag):::s))
     Q.
Proof.
  eapply push_spec.
Qed.

Lemma pop_spec: forall Q,
  HT pop
     (fun m s => exists v vl s0, s = (v,vl):::s0 /\ Q m s0)
     Q.
Proof.
  unfold HT, pop.
  split_vc; simpl; run1.
Qed.

Lemma genAnd_spec : forall (Q:memory -> stack -> Prop),
  HT genAnd
     (fun m s => exists b1 b2 s0, s = (boolToZ b1,handlerTag):::(boolToZ b2,handlerTag):::s0 /\
                                  Q m ((boolToZ (andb b1 b2),handlerTag):::s0))
     Q.
Proof.
  intros.
  eapply HT_strengthen_premise with
     (fun m s => exists b1 b2 s0 m0, s = (boolToZ b1,handlerTag):::(boolToZ b2,handlerTag):::s0 /\ m = m0 /\
                                     Q m0 ((boolToZ (andb b1 b2),handlerTag):::s0)).


  eapply HT_forall_exists.  intro b1.
  eapply HT_forall_exists.  intro b2.
  eapply HT_forall_exists.  intro s0.
  eapply HT_forall_exists.  intro m1.

  destruct b1; eapply HT_strengthen_premise.
  eapply ifNZ_spec_NZ with (v:=1).
  apply nop_spec.
  omega.
  simpl; intuition eauto; subst. eauto.
  split_vc; subst. auto.

  eapply ifNZ_spec_existential.
  apply nop_spec.
  eapply HT_compose_bwd.
  eapply genFalse_spec.
  eapply pop_spec.
  split_vc.

  split_vc.
Qed.

Lemma genOr_spec : forall (Q:memory -> stack -> Prop),
  HT genOr
     (fun m s => exists b1 b2 s0, s = (boolToZ b1,handlerTag):::(boolToZ b2,handlerTag):::s0 /\
                                  Q m ((boolToZ (orb b1 b2),handlerTag):::s0))
     Q.
Proof.
  intros.
  eapply HT_strengthen_premise with
     (fun m s => exists b1 b2 s0 m0, s = (boolToZ b1,handlerTag):::(boolToZ b2,handlerTag):::s0 /\ m = m0 /\
                                     Q m0 ((boolToZ (orb b1 b2),handlerTag):::s0)).
  eapply HT_forall_exists.  intro b1.
  eapply HT_forall_exists.  intro b2.
  eapply HT_forall_exists.  intro s0.
  eapply HT_forall_exists.  intro m1.

  destruct b1; eapply HT_strengthen_premise.

    eapply ifNZ_spec_NZ with (v:=1).
    eapply HT_compose_bwd.
    eapply genTrue_spec.
    eapply pop_spec.
    omega.

    split_vc. subst; auto.

    eapply ifNZ_spec_Z with (v:=0).
    apply nop_spec.
    reflexivity.
    split_vc. subst; auto.

    split_vc.
Qed.

Definition negz (z: Z) : Z :=
  match z with
      | 0 => 1
      | _ => 0
  end.

Lemma genNot_spec: forall Q,
  HT genNot
     (fun m s => exists z s0,
                   s = (z, handlerTag) ::: s0
                   /\ Q m ((negz z,handlerTag) ::: s0))
     Q.
Proof.
  intros. unfold genNot.
  eapply HT_strengthen_premise.
  eapply ifNZ_spec_existential.
  eapply genFalse_spec.
  eapply genTrue_spec.
  split_vc. subst; intuition; (destruct x eqn:?; try intuition); try congruence.
Qed.

Lemma genImpl_spec: forall b1 b2, forall m0 s0,
  HT genImpl
     (fun m s => m = m0 /\ s = CData (boolToZ b1,handlerTag) ::
                               CData (boolToZ b2,handlerTag) :: s0)
     (fun m s => m = m0 /\ s = CData (boolToZ (implb b1 b2),handlerTag) :: s0).
Proof.
  intros.
  unfold genImpl.
  eapply HT_compose_bwd.
  eapply genOr_spec.
  eapply HT_strengthen_premise.
  eapply genNot_spec.
  intros; simpl. inv H; subst.
  exists (boolToZ b1) ; exists ((boolToZ b2, handlerTag) ::: s0).
  split; eauto.
  unfold boolToZ in *.
  (destruct b1 eqn:?; destruct b2 eqn:?; try intuition); simpl.
  exists false; exists true;  eauto.
  exists false; exists false;  eauto.
  exists true; exists true;  eauto.
  exists true; exists false;  eauto.
Qed.

(* NC: use [Z.eqb_eq] and [Z.eqb_neq] to relate the boolean equality
   to propositional equality. *)
Lemma genTestEqual_spec: forall c1 c2, forall v1 v2, forall m0,
  (forall s0,
     HT c1
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (v1,handlerTag) ::: s0)) ->
  (forall s0,
     HT c2
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (v2,handlerTag) ::: s0)) ->
  (forall s0,
     HT (genTestEqual c1 c2)
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (boolToZ (v1 =? v2),handlerTag) ::: s0)).
Proof.
  intros.
  unfold genTestEqual.
  eapply HT_compose_bwd; eauto.
  eapply HT_compose_bwd; eauto.
  eapply HT_compose_bwd.

  eapply (genNot_spec); eauto.
  eapply HT_strengthen_premise.
  eapply sub_spec.
  split_vc; subst.
  repeat f_equal; eauto.
  destruct (Z.eq_dec v1 v2); subst.
  - rewrite <- Zminus_diag_reverse.
    rewrite Z.eqb_refl.
    reflexivity.
  - generalize n. intros. rewrite <- Z.eqb_neq in n.
    rewrite n.
    destruct (v2 - v1) eqn:E; try omega; simpl; eauto.
Qed.


(** * Some specs of [cases] combinator, expressed with ghost variables *)
Lemma cases_spec_base_GT_specialized: forall cnil P Qnil,
  GT cnil P Qnil ->
  GT (cases [] cnil) P Qnil.
Proof.
unfold GT; intros; eapply cases_spec_base.
  eapply HT_strengthen_premise; eauto.
Qed.

Definition GT_push_v (c: code) (P: HProp) (v: HFun): Prop :=
  GT c P (fun m0 s0 m s => P m0 s0 /\
                           m = m0 /\
                           s = CData (v m0 s0, handlerTag) :: s0).
Definition GT_guard_v (b: code) (P: HProp) (v: HFun) (Q: GProp): Prop :=
  GT b (fun m s => P m s /\ v m s <> 0) Q.

Lemma cases_spec_step_GT_specialized: forall c v b cbs cnil P Qb Qcbs,
  GT_push_v c P v ->
  GT_guard_v b P v Qb ->
  GT (cases cbs cnil) P Qcbs ->
  GT (cases ((c,b)::cbs) cnil)
     P
     (fun m0 s0 m s => (v m0 s0 <> 0 -> Qb m0 s0 m s) /\
                       (v m0 s0 = 0 -> Qcbs m0 s0 m s)).
Proof.
  intros c vc b cbs d P Qb Qcbs Hc Hb Hcbs.
  intros m0 s0.
  pose (Hc m0 s0) as Hcm0s0.
  eapply ite_spec with (Pt := (fun m s => P m0 s0 /\ m = m0 /\ s = s0 /\ vc m0 s0 <> 0))
                       (Pf := (fun m s => P m0 s0 /\ m = m0 /\ s = s0 /\ vc m0 s0 =  0)).
  eapply HT_weaken_conclusion.
  exact Hcm0s0.

  intuition.
  exists (vc m0 s0).
  exists handlerTag.
  exists s0.
  intuition; subst; auto.

  apply (HT_consequence' _ _ _ _ _ (Hb m0 s0)); intuition.
  destruct H as (? & ? & ? & ? & ? & H).
  exfalso. auto.

  fold cases.
  apply (HT_consequence' _ _ _ _ _ (Hcbs m0 s0)); intuition.
  destruct H as (? & ? & ? & ? & ? & H).
  exfalso. auto.
Qed.



(** Proof of a specification for the switch-case generator indexed by type [I]. *)
Section IndexedCasesSpec.

Variable cnil: code.
Variable Qnil: GProp.
Variable I: Type.
Variable genC genB: I -> code.
Variable genQ: I -> GProp.
Variable genV: I -> HFun.

Definition indexed_post: (list I) -> GProp :=
  fix f (indices: list I) :=
    fun m0 s0 m s =>
      match indices with
      | []            => Qnil m0 s0 m s
      | i :: indices' => (genV i m0 s0 <> 0 -> genQ i m0 s0 m s) /\
                         (genV i m0 s0 =  0 -> f indices' m0 s0 m s)
      end.

Variable P: HProp.
Definition indexed_hyps: (list I) -> Prop :=
  fix f (indices: list I) :=
    match indices with
    | []            => True
    | i :: indices' => GT_push_v (genC i) P (genV i) /\
                       GT_guard_v (genB i) P (genV i) (genQ i) /\
                       f indices'
    end.

Lemma indexed_cases_spec: forall is,
  GT cnil P Qnil ->
  indexed_hyps is ->
  GT (indexed_cases cnil genC genB is)
     P
     (indexed_post is).
Proof.
  induction is; intros.
  - eapply cases_spec_base_GT_specialized; eauto.
  - simpl in *.
    eapply cases_spec_step_GT_specialized; intuition auto.
Qed.

End IndexedCasesSpec.

(** * HTEscape specification for escaping code *)

Lemma ret_specEscape: forall raddr (P: HProp),
  HTEscape raddr [Ret]
    (fun m s => exists s', s = (CRet raddr false false::s') /\ P m s')
    (fun m s => (P m s , Success)).
Proof.
  intros. destruct raddr eqn:E; subst.
  unfold HTEscape.
  split_vc; subst.

  (* Run an instruction *)
  eapply rte_success; auto.
  eapply ruu_end; simpl; eauto.
  eapply cstep_ret_p; auto.
  eapply cptr_done.
Qed.

Lemma jump_specEscape_Failure: forall tag raddr (P: HProp),
  HTEscape raddr [Jump]
           (fun m s => exists s0, (-1, tag) ::: s0 = s /\ P m s0)
           (fun m s => (P m s , Failure)).
Proof.
  intros.
  unfold HTEscape.
  split_vc; subst.

  (* Run an instruction *)
  eapply rte_fail; auto.
  eapply rte_step; eauto.
  eapply cstep_jump_p; auto.
  simpl; eauto; omega.
Qed.

Lemma skipNZ_specEscape: forall r c1 c2 v P1 P2 Q,
  (v =  0 -> HTEscape r c1 P1 Q) ->
  (v <> 0 -> HTEscape r c2 P2 Q) ->
  HTEscape r ((skipNZ (length c1) ++ c1) ++ c2)
           (fun m s => exists s0, s = (v, handlerTag) ::: s0 /\
                                  (v =  0 -> P1 m s0) /\
                                  (v <> 0 -> P2 m s0))
           Q.
Proof.
  intros.
  unfold skipNZ.
  destruct (dec_eq v 0); subst.
  - eapply HTEscape_append.
    eapply HTEscape_compose.
    eapply skipNZ_spec_Z; auto.
    eapply HTEscape_strengthen_premise; intuition eauto.
  - eapply HTEscape_compose.
    eapply skipNZ_continuation_spec_NZ; auto.
    eapply HTEscape_strengthen_premise; intuition eauto.
Qed.

Lemma ifNZ_specEscape: forall r t f v Pt Pf Q,
  (v <> 0 -> HTEscape r t Pt Q) ->
  (v =  0 -> HTEscape r f Pf Q) ->
  HTEscape r (ifNZ t f)
           (fun m s => exists s0, s = (v, handlerTag) ::: s0 /\
                                  (v <> 0 -> Pt m s0) /\
                                  (v =  0 -> Pf m s0))
           Q.
Proof.
  intros.
  unfold ifNZ.
  rewrite <- app_ass.
  eapply HTEscape_strengthen_premise.
  eapply skipNZ_specEscape with (v:=v).
  - intros.
    eapply HTEscape_append; eauto.
  - intros.
    eauto.
  - intros m s (s0 & ? & H1 & H2); subst; eauto.
Qed.

End CodeSpecs.
