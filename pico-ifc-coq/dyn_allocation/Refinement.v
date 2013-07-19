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

Definition refinement_statement match_init_data
                                match_events
                                observe1 observe2 :=
  forall i1 i2 t2 s2,
    match_init_data i1 i2 ->
    @TINI.exec S2 (init_state S2 i2) t2 s2 ->
    exists t1 s1,
      @TINI.exec S1 (init_state S1 i1) t1 s1 /\
      match_traces match_events
                   (observe1 t1) (observe2 t2).

Record refinement := {
  ref_match_init_data : init_data S1 -> init_data S2 -> Prop;
  ref_match_events : event S1 -> event S2 -> Prop;
  ref_observe1 : trace1 -> trace1;
  ref_observe2 : trace2 -> trace2;
  ref_prop : refinement_statement ref_match_init_data
                                  ref_match_events
                                  ref_observe1 ref_observe2
}.

Definition state_refinement_statement match_states
                                      match_events
                                      observe1 observe2 :=
  forall s1 s2 t2 s2',
    match_states s1 s2 ->
    @TINI.exec S2 s2 t2 s2' ->
    exists t1 s1',
      @TINI.exec S1 s1 t1 s1' /\
      match_traces match_events
                   (observe1 t1) (observe2 t2).

Record state_refinement := {
  sref_match_states : state S1 -> state S2 -> Prop;
  sref_match_events : event S1 -> event S2 -> Prop;
  sref_observe1 : trace1 -> trace1;
  sref_observe2 : trace2 -> trace2;
  sref_prop : state_refinement_statement sref_match_states
                                         sref_match_events
                                         sref_observe1 sref_observe2
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
                       (sref_match_events SR)
                       (sref_observe1 SR) (sref_observe2 SR).
Proof.
  unfold refinement_statement. eauto using (sref_prop SR).
Qed.

Definition refinement_from_state_refinement : refinement :=
  {| ref_match_init_data := match_init_data
   ; ref_match_events := sref_match_events SR
   ; ref_observe1 := sref_observe1 SR
   ; ref_observe2 := sref_observe2 SR
   ; ref_prop := refinement_from_state_refinement_prop |}.

End RefinementFromStateRefinement.

Context {observer : Type}
        {O1 : TINI.Observation S1 observer}
        {O2 : TINI.Observation S2 observer}.

Section Weaken.

Variable R : refinement.

Variable observe1 : trace1 -> trace1.
Variable observe2 : trace2 -> trace2.

Definition observations_compatible :=
  forall t1 t2,
    match_traces (ref_match_events R) (ref_observe1 R t1) (ref_observe2 R t2) ->
    match_traces (ref_match_events R) (observe1 t1) (observe2 t2).

Hypothesis oc : observations_compatible.

Lemma weaken_refinement_prop :
  refinement_statement (ref_match_init_data R)
                       (ref_match_events R)
                       observe1 observe2.
Proof.
  intros until 2.
  exploit (ref_prop R); eauto.
  intros [? [? [? ?]]]; eauto.
Qed.

Definition weaken_refinement : refinement :=
 {| ref_match_init_data := ref_match_init_data R
  ; ref_match_events := ref_match_events R
  ; ref_observe1 := observe1
  ; ref_observe2 := observe2
  ; ref_prop := weaken_refinement_prop |}.

End Weaken.

Section NI.

Variable R : refinement.

Hypothesis oc :
  forall o, observations_compatible R
                                    (TINI.observe O1 o) (TINI.observe O2 o).

Hypothesis noninterference1 : TINI.tini O1.
Hypothesis i_equiv2_i_equiv1 : forall o i21 i22,
                                 TINI.i_equiv o i21 i22 ->
                                 exists i11 i12,
                                   TINI.i_equiv o i11 i12 /\
                                   ref_match_init_data R i11 i21 /\
                                   ref_match_init_data R i12 i22.
Hypothesis match_events_equiv : forall o e11 e12 e21 e22,
                                  TINI.e_equiv _ o e11 e12 ->
                                  ref_match_events R e11 e21 ->
                                  ref_match_events R e12 e22 ->
                                  TINI.e_equiv _ o e21 e22.

Theorem refinement_preserves_noninterference : TINI.tini O2.
Proof.
  intros o i21 t21 s21' i22 t22 s22' Heq2 Hexec21 Hexec22.
  assert (ref' := weaken_refinement_prop (oc o)).
  assert (H := i_equiv2_i_equiv1 _ _ _ Heq2).
  destruct H as [i11 [i12 [Heq1 [Hm1 Hm2]]]].
  assert (H := ref' _ _ _ _ Hm1 Hexec21).
  destruct H as [t11 [s11' [Hexec11 Hmt1]]].
  assert (H := ref' _ _ _ _ Hm2 Hexec22).
  destruct H as [t12 [s12' [Hexec12 Hmt2]]].
  assert (Hindist := noninterference1 _ _ _ Heq1 Hexec11 Hexec12).
  generalize (TINI.observe_forall _ o t22). intros.
  generalize (TINI.observe_forall _ o t21). intros.
  gdep (TINI.observe O2 o t22). gdep (TINI.observe O2 o t21).
  gdep (TINI.observe O1 o t12). gdep (TINI.observe O1 o t11).
  clear - match_events_equiv.

  intros t11 t12 Hindist.
  induction Hindist as [| |e1 t11' t12'];
  intros t21 Hmt1 Ht21 t22 Hmt2 Ht22;
  inv Hmt1; inv Hmt2; try constructor; eauto.
  match goal with
    | |- TINI.ti_trace_indist (?E1 :: _) (?E2 :: _) =>
      assert (Heq : TINI.e_equiv _ o E1 E2)
        by (eapply match_events_equiv; eauto; reflexivity)
  end.
  inv Ht21. inv Ht22. inv Heq; intuition.
  constructor. auto.
Qed.

End NI.

Section Strong.

Variable match_events : event S1 -> event S2 -> Prop.
Variable match_states : state S1 -> state S2 -> Prop.

(* To be used in the abstract <-> quasi-abtract layer *)
Hypothesis lockstep : forall s11 s21 e2 s22,
                        match_states s11 s21 ->
                        step S2 s21 e2 s22 ->
                        exists e1 s12,
                          step S1 s11 e1 s12 /\ match_events e1 e2 /\ match_states s12 s22.

Theorem strong_refinement_prop :
  state_refinement_statement match_states
                             match_events
                             (fun x => x) (fun x => x).
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
    match goal with
      | H1 : step S1 _ ?e1 _,
        H2 : @TINI.exec S1 _ ?t1 ?s12 |- _ =>
        exists (e1 :: t1)
    end.
    eauto.
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
Hypothesis oe : ref_observe2 R12 = ref_observe1 R23.

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

Lemma ref_composition_prop : refinement_statement match_init_data match_events
                                                  (ref_observe1 R12)
                                                  (ref_observe2 R23).
Proof.
  intros s11 s31 t3 s32 H13 Hexec3.
  exploit mid13; eauto.
  intros [s2 [H12 H23]].
  exploit (ref_prop R23); eauto.
  intros [? [? [? ?]]].
  exploit (ref_prop R12); eauto.
  intros H'.
  destruct H' as [? [? [? ?]]].
  rewrite oe in *.
  eauto using match_events_composition.
Qed.

Definition ref_composition :=
  {| ref_prop := ref_composition_prop |}.

End Composition.

Section Silent.

Variable state1 : Type.
Variable event1 : Type.
Variable step1 : state1 -> option event1 -> state1 -> Prop.
Variable init_data1 : Type.
Variable init_state1 : init_data1 -> state1.

Let sem1 : semantics := {|
  state := state1;
  event := option event1;
  step := step1;
  init_data := init_data1;
  init_state := init_state1
|}.

Variable state2 : Type.
Variable event2 : Type.
Variable step2 : state2 -> option event2 -> state2 -> Prop.
Variable init_data2 : Type.
Variable init_state2 : init_data2 -> state2.

Let sem2 : semantics := {|
  state := state2;
  event := option event2;
  step := step2;
  init_data := init_data2;
  init_state := init_state2
|}.

Variable match_events : option event1 -> option event2 -> Prop.

Context {observer : Type}
        {O1 : TINI.Observation sem1 observer}
        {O2 : TINI.Observation sem2 observer}.

Hypothesis silent_high1 : forall o, ~ @TINI.e_low sem1 _ _ o None.
Hypothesis silent_high2 : forall o, ~ @TINI.e_low sem2 _ _ o None.
Hypothesis match_events_low :
  forall e1 e2 o, match_events e1 e2 -> (@TINI.e_low sem1 _ _ o e1 <->
                                         @TINI.e_low sem2 _ _ o e2).

Lemma remove_none_observe1 : forall t o, @TINI.observe sem1 _ _ o (remove_none t) =
                                         @TINI.observe sem1 _ _ o t.
Proof.
  induction t as [|e t IH]; simpl; auto.
  destruct e as [e|]; simpl; auto; intros o.
  - rewrite IH. reflexivity.
  - match goal with
      | |- context[if ?b then true else false] =>
        destruct b
    end; auto.
    exfalso.
    eapply silent_high1; eauto.
Qed.

Lemma remove_none_observe2 : forall t o, @TINI.observe sem2 _ _ o (remove_none t) =
                                         @TINI.observe sem2 _ _ o t.
Proof.
  induction t as [|e t IH]; simpl; auto.
  destruct e as [e|]; simpl; auto; intros o.
  - rewrite IH. reflexivity.
  - match goal with
      | |- context[if ?b then true else false] =>
        destruct b
    end; auto.
    exfalso.
    eapply silent_high2; eauto.
Qed.

Lemma observations_compatible_option :
  forall o t1 t2,
    match_traces sem1 sem2 match_events
                 (remove_none t1) (remove_none t2) ->
    match_traces sem1 sem2 match_events
                 (@TINI.observe sem1 _ _ o t1) (@TINI.observe sem2 _ _ o t2).
Proof.
  intros o t1 t2 H.
  remember (remove_none t2) as t2'. gdep t2.
  remember (remove_none t1) as t1'. gdep t1.
  induction H as [|e1' t1' e2' t2' H MATCH IH];
  intros t1 H1 t2 H2;
  simpl in *.
  - rewrite <- remove_none_observe1.
    rewrite <- H1. simpl.
    rewrite <- remove_none_observe2.
    rewrite <- H2. simpl.
    constructor.
  - unfold remove_none in H1, H2.
    apply filter_cons_inv_strong in H1.
    destruct H1 as [t11 [t12 [H11 [H12 H13]]]]. subst.
    apply filter_cons_inv_strong in H2.
    destruct H2 as [t21 [t22 [H21 [H22 H23]]]]. subst.
    exploit IH; unfold remove_none; eauto.
    clear IH MATCH.
    intros MATCH.
    assert (E : @TINI.observe sem1 _ _ o (t11 ++ t12) =
                @TINI.observe sem1 _ _ o t11 ++
                @TINI.observe sem1 _ _ o t12) by
        apply filter_app.
    rewrite E. clear E.
    assert (E : @TINI.observe sem2 _ _ o (t21 ++ t22) =
                @TINI.observe sem2 _ _ o t21 ++
                @TINI.observe sem2 _ _ o t22) by
        apply filter_app.
    rewrite E. clear E.
    rewrite <- remove_none_observe1.
    rewrite <- remove_none_observe2.
    unfold remove_none.
    rewrite H12. rewrite H22. simpl.
    repeat match goal with
             | |- context [if ?b then true else false] =>
               destruct b
           end;
    simpl; try constructor; auto;
    eapply match_events_low with (o := o) in H; intuition.
Qed.

End Silent.
