Require Import Relations.
Require Import List.
Require Import Utils.
Require Import Semantics.
Require TINI.

Set Implicit Arguments.
Hint Constructors TINI.exec.

Section Refinement.

Variable S1 : semantics.
Let trace1 := list (event S1).

Variable S2 : semantics.
Let trace2 := list (event S2).

Inductive match_traces (match_events : event S1 -> event S2 -> Prop)
  : trace1 -> trace2 -> Prop :=
| mt_nil : match_traces match_events nil nil
| mt_cons : forall e1 t1 e2 t2,
              match_events e1 e2 ->
              match_traces match_events t1 t2 ->
              match_traces match_events (e1 :: t1) (e2 :: t2).
Hint Constructors match_traces.

Lemma match_traces_no_filter:
  forall (match_events: event S1 -> event S2 -> Prop) tr1 tr2,
    match_traces match_events tr1 tr2 ->
      length tr1 = length tr2.
Proof.
  intros hme tr1 tr2 hmt.
  induction hmt; auto. simpl. rewrite IHhmt. auto.
Qed.

Definition refinement_statement match_init_data
                                match_events :=
  forall i1 i2 t2 s2,
    match_init_data i1 i2 ->
    @TINI.exec S2 (init_state S2 i2) t2 s2 ->
    exists t1 s1,
      @TINI.exec S1 (init_state S1 i1) t1 s1 /\
      match_traces match_events t1 t2.

Record refinement := {
  ref_match_init_data : init_data S1 -> init_data S2 -> Prop;
  ref_match_events : event S1 -> event S2 -> Prop;
  ref_prop : refinement_statement ref_match_init_data
                                  ref_match_events
}.

Definition state_refinement_statement match_states
                                      match_events :=
  forall s1 s2 t2 s2',
    match_states s1 s2 ->
    @TINI.exec S2 s2 t2 s2' ->
    exists t1 s1',
      @TINI.exec S1 s1 t1 s1' /\
      match_traces match_events t1 t2.


Record state_refinement := {
  sref_match_states : state S1 -> state S2 -> Prop;
  sref_match_events : event S1 -> event S2 -> Prop;
  sref_prop : state_refinement_statement sref_match_states
                                         sref_match_events
}.

Section RefinementFromStateRefinement.

Variable SR : state_refinement.

Variable match_init_data : init_data S1 -> init_data S2 -> Prop.

Hypothesis match_init_data_match_states :
  forall i1 i2,
    match_init_data i1 i2 ->
    sref_match_states SR (init_state _ i1) (init_state _ i2).

Lemma refinement_from_state_refinement_prop :
  refinement_statement match_init_data
                       (sref_match_events SR).
Proof.
  unfold refinement_statement. eauto using (sref_prop SR).
Qed.

Definition refinement_from_state_refinement : refinement :=
  {| ref_match_init_data := match_init_data
   ; ref_match_events := sref_match_events SR
   ; ref_prop := refinement_from_state_refinement_prop |}.

End RefinementFromStateRefinement.

Context {e_obs : Type}
        {O1 : TINI.Observation S1 e_obs}
        {O2 : TINI.Observation S2 e_obs}.

Section NI.

Variable R : refinement.

Hypothesis noninterference1 : TINI.tini O1.

Let low_compatible o1 o2 :=
  forall e1 e2,
    ref_match_events R e1 e2 ->
    (TINI.e_low (S:=S1) o1 (TINI.out e1) <-> TINI.e_low (S:=S2) o2 (TINI.out e2)).

Let i_equiv1_i_equiv2 o1 o2 :=
  forall i21 i22,
    TINI.i_equiv o2 i21 i22 ->
    exists i11 i12,
      TINI.i_equiv o1 i11 i12 /\
      ref_match_init_data R i11 i21 /\
      ref_match_init_data R i12 i22.

Let a_equiv1_a_equiv2 o1 o2 :=
  forall e11 e12 e21 e22,
    TINI.a_equiv _ o1 (E e11) (E e12) ->
    ref_match_events R e11 e21 ->
    ref_match_events R e12 e22 ->
    TINI.a_equiv _ o2 (E e21) (E e22).

Lemma match_traces_match_observations :
  forall o1 o2 t1 t2
         (COMP : low_compatible o1 o2)
         (TRACES : match_traces (ref_match_events R) t1 t2),
    match_traces (ref_match_events R)
                 (TINI.observe O1 o1 t1) (TINI.observe O2 o2 t2).
Proof.
  intros.
  induction TRACES; simpl; auto.
  exploit COMP; eauto. intros [COMP1 COMP2].
  destruct (TINI.e_low_dec (S:=S1) o1 (TINI.out e1)) as [E1 | E1];
  destruct (TINI.e_low_dec (S:=S2) o2 (TINI.out e2)) as [E2 | E2];
  intuition.
Qed.

Definition tini_preservation_hypothesis :=
  forall o2, exists o1,
    low_compatible o1 o2 /\
    i_equiv1_i_equiv2 o1 o2 /\
    a_equiv1_a_equiv2 o1 o2.

Hypothesis compatibility : tini_preservation_hypothesis.

Theorem refinement_preserves_noninterference : TINI.tini O2.
Proof.
  intros o2 i21 t21 s21' i22 t22 s22' Heq2 Hexec21 Hexec22.
  destruct (compatibility o2) as [o1 [H1 [H2 H3]]].
  assert (H := H2 _ _ Heq2).
  destruct H as [i11 [i12 [Heq1 [Hm1 Hm2]]]].
  assert (H := ref_prop R _ _ Hm1 Hexec21).
  destruct H as [t11 [s11' [Hexec11 Hmt1]]].
  assert (H := ref_prop R _ _ Hm2 Hexec22).
  destruct H as [t12 [s12' [Hexec12 Hmt2]]].
  assert (Hindist := noninterference1 _ _ _ Heq1 Hexec11 Hexec12).
  generalize (match_traces_match_observations H1 Hmt1). clear Hmt1. intros Hmt1.
  generalize (match_traces_match_observations H1 Hmt2). clear Hmt2. intros Hmt2.
  generalize (TINI.observe_forall _ o2 t22). intros.
  generalize (TINI.observe_forall _ o2 t21). intros.
  gdep (TINI.observe O2 o2 t22). gdep (TINI.observe O2 o2 t21).
  gdep (TINI.observe O1 o1 t12). gdep (TINI.observe O1 o1 t11).
  clear - H1 H3.

  induction t; destruct t0; intros Hi; intros.
  + inv Hi; constructor.
  + inv Hi.
  + inv Hmt2; constructor.
  + inv Hmt2; inv Hmt1.
    simpl.
    assert (TINI.a_equiv O2 o2 (E e0) (E e2)).
      eapply H3; eauto.
      constructor 2.
      inv Hi; auto.
      rewrite (H1 a e0); auto.
      inv H0; auto.
      rewrite (H1 e e2); auto.
      inv H; auto.
    assert (T:TINI.ti_trace_indist
                                 (map (TINI.out (S:=S2)) t3)
                                 (map (TINI.out (S:=S2)) t4)).
      eapply IHt; eauto.
      simpl in Hi; inv Hi; auto.
      inv H0; auto.
      inv H; auto.
    inv H2.
    * rewrite H10; constructor; auto.
    * elim H10; inv H0; auto.
Qed.

End NI.

Section Strong.

Variable match_events : event S1 -> event S2 -> Prop.
Variable match_states : state S1 -> state S2 -> Prop.

Let match_actions e1 e2 := match_actions match_events e1 e2.

(* To be used in the abstract <-> quasi-abtract layer *)
Hypothesis lockstep : forall s11 s21 e2 s22,
                        match_states s11 s21 ->
                        step S2 s21 e2 s22 ->
                        exists e1 s12,
                          step S1 s11 e1 s12 /\ match_actions e1 e2 /\ match_states s12 s22.

Theorem strong_refinement_prop :
  state_refinement_statement match_states
                             match_events.
Proof.
  intros s11 s21 t2 s22 Hmt Hexec2.
  gdep s11.
  induction Hexec2; intros s11 Hmt.
  - repeat eexists; eauto.
  - match goal with
      | H1 : match_states _ _,
        H2 : step _ _ _ _ |- _ =>
        exploit lockstep; eauto;
        intros Hlock;
        destruct Hlock as [? [? [? [? ?]]]]
    end.
    match goal with
      | H : match_states _ _ |- _ =>
        apply IHHexec2 in H;
        destruct H as [? [? [? ?]]]
    end.
    inv H1.
    match goal with
      | H1 : step S1 _ (E ?e1) _,
        H2 : @TINI.exec S1 _ ?t1 ?s12 |- _ =>
        exists (e1 :: t1)
    end.
    eauto.
  -  exploit lockstep; eauto.
     intros (a1 & s12 & T1 & T2 & T3).
     apply IHHexec2 in T3.
     destruct T3 as (t1 & s1' & V1 & V2).
     inv T2; eauto.
Qed.

Definition strong_refinement : state_refinement :=
  {| sref_prop := strong_refinement_prop |}.

End Strong.

End Refinement.

Section Composition.

Variable S1 : semantics.
Variable S2 : semantics.
Variable S3 : semantics.

Variable R12 : refinement S1 S2.
Variable R23 : refinement S2 S3.

Variable match_init_data : init_data S1 -> init_data S3 -> Prop.
Variable match_events : event S1 -> event S3 -> Prop.

Hypothesis mid13 : forall s1 s3,
                     match_init_data s1 s3 ->
                     exists s2,
                       ref_match_init_data R12 s1 s2 /\
                       ref_match_init_data R23 s2 s3.
Hypothesis me13 : forall e1 e2 e3,
                    ref_match_events R12 e1 e2 ->
                    ref_match_events R23 e2 e3 ->
                    match_events e1 e3.

Lemma match_events_composition : forall t1 t2 t3,
                                   match_traces S1 S2
                                                (ref_match_events R12) t1 t2 ->
                                   match_traces S2 S3
                                                (ref_match_events R23) t2 t3 ->
                                   match_traces S1 S3 match_events t1 t3.
Proof.
  intros t1 t2 t3 H12.
  gdep t3.
  induction H12; intros t3 H23; inv H23; econstructor; eauto.
Qed.

Lemma ref_composition_prop : refinement_statement S1 S3 match_init_data match_events.
Proof.
  intros s11 s31 t3 s32 H13 Hexec3.
  exploit mid13; eauto.
  intros [s2 [H12 H23]].
  exploit (ref_prop R23); eauto.
  intros [? [? [? ?]]].
  exploit (ref_prop R12); eauto.
  intros H'.
  destruct H' as [? [? [? ?]]].
  eauto using match_events_composition.
Qed.

Definition ref_composition :=
  {| ref_prop := ref_composition_prop |}.

End Composition.
