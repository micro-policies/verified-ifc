Require Import Relations.
Require Import List.
Require Import Utils.
Require TINI.

Set Implicit Arguments.
Hint Constructors TINI.exec.

Section Refinement.

Variable state1 : Type.
Variable event1 : Type.
Variable step1 : state1 -> event1 -> state1 -> Prop.
Let trace1 := list event1.

Variable state2 : Type.
Variable event2 : Type.
Variable step2 : state2 -> event2 -> state2 -> Prop.
Let trace2 := list event2.

Variable match_states : state1 -> state2 -> Prop.
Variable match_events : event1 -> event2 -> Prop.

Inductive match_traces : trace1 -> trace2 -> Prop :=
| mt_nil : match_traces nil nil
| mt_cons : forall e1 t1 e2 t2,
              match_events e1 e2 ->
              match_traces t1 t2 ->
              match_traces (e1 :: t1) (e2 :: t2).
Hint Constructors match_traces.

Section Simulation.

Variable observe1 : trace1 -> trace1.
Variable observe2 : trace2 -> trace2.

Definition backward_simulation :=
  forall s1 s2 t2 s2',
    match_states s1 s2 ->
    TINI.exec step2 s2 t2 s2' ->
    exists t1 s1',
      TINI.exec step1 s1 t1 s1' /\ match_traces (observe1 t1) (observe2 t2).

End Simulation.

Context {observer : Type}
        {OE1 : TINI.ObservableEvent observer event1}
        {OE2 : TINI.ObservableEvent observer event2}.

Variable s_equiv1 : observer -> relation state1.
Variable s_equiv2 : observer -> relation state2.

Section NI.

Hypothesis bs : forall o, backward_simulation (TINI.observe o) (TINI.observe o).
Hypothesis noninterference1 : TINI.tini step1 s_equiv1.
Hypothesis match_states_eq : forall o s21 s22,
                               s_equiv2 o s21 s22 ->
                               exists s11 s12,
                                 s_equiv1 o s11 s12 /\
                                 match_states s11 s21 /\
                                 match_states s12 s22.
Hypothesis match_events_equiv : forall o e11 e12 e21 e22,
                                  TINI.e_equiv o e11 e12 ->
                                  match_events e11 e21 ->
                                  match_events e12 e22 ->
                                  TINI.e_equiv o e21 e22.

Theorem noninterference2 : TINI.tini step2 s_equiv2.
Proof.
  intros o s21 t21 s21' s22 t22 s22' Heq2 Hexec21 Hexec22.
  assert (H := match_states_eq Heq2).
  destruct H as [s11 [s12 [Heq1 [Hm1 Hm2]]]].
  assert (H := bs o Hm1 Hexec21).
  destruct H as [t11 [s11' [Hexec11 Hmt1]]].
  assert (H := bs o Hm2 Hexec22).
  destruct H as [t12 [s12' [Hexec12 Hmt2]]].
  assert (Hindist := noninterference1 Heq1 Hexec11 Hexec12).
  gdep (TINI.observe o t22). gdep (TINI.observe o t21).
  gdep (TINI.observe o t12). gdep (TINI.observe o t11).
  clear - match_events_equiv.

  intros t11 t12 Hindist.
  induction Hindist as [| |e11 e12 t11' t12'];
  intros t21 Hmt1 t22 Hmt2;
  inv Hmt1; inv Hmt2; constructor; eauto.
Qed.

End NI.

Section Strong.

(* To be used in the abstract <-> quasi-abtract layer *)

Hypothesis lockstep : forall s11 s21 e2 s22,
                        match_states s11 s21 ->
                        step2 s21 e2 s22 ->
                        exists e1 s12,
                          step1 s11 e1 s12 /\ match_events e1 e2 /\ match_states s12 s22.

Theorem strong_backward_simulation : backward_simulation (fun x => x) (fun x => x).
Proof.
  intros s11 s21 t2 s22 Hmt Hexec2.
  gdep s11.
  induction Hexec2; intros s11 Hmt.
  - repeat eexists; eauto.
  - match goal with
      | H1 : match_states _ _,
        H2 : step2 _ _ _ |- _ =>
        generalize (lockstep H1 H2);
        intros Hlock;
        destruct Hlock as [? [? [? [? ?]]]]
    end.
    match goal with
      | H : match_states _ _ |- _ =>
        apply IHHexec2 in H;
        destruct H as [? [? [? ?]]]
    end.
    match goal with
      | H1 : step1 _ ?e1 _,
        H2 : TINI.exec step1 _ ?t1 ?s12 |- _ =>
        exists (e1 :: t1)
    end.
    eauto.
Qed.

End Strong.

End Refinement.

Section Composition.

Variable state1 : Type.
Variable event1 : Type.
Variable step1 : state1 -> event1 -> state1 -> Prop.
Let trace1 := list event1.
Variable observe1 : trace1 -> trace1.

Variable state2 : Type.
Variable event2 : Type.
Variable step2 : state2 -> event2 -> state2 -> Prop.
Let trace2 := list event2.
Variable observe2 : trace2 -> trace2.

Variable state3 : Type.
Variable event3 : Type.
Variable step3 : state3 -> event3 -> state3 -> Prop.
Let trace3 := list event3.
Variable observe3 : trace3 -> trace3.

Variable match_states12 : state1 -> state2 -> Prop.
Variable match_events12 : event1 -> event2 -> Prop.

Variable match_states23 : state2 -> state3 -> Prop.
Variable match_events23 : event2 -> event3 -> Prop.

Let match_states13 s1 s3 := exists s2, match_states12 s1 s2 /\
                                       match_states23 s2 s3.
Let match_events13 e1 e3 := exists e2, match_events12 e1 e2 /\
                                       match_events23 e2 e3.

Lemma match_events_composition : forall t1 t2 t3,
                                   match_traces match_events12 t1 t2 ->
                                   match_traces match_events23 t2 t3 ->
                                   match_traces match_events13 t1 t3.
Proof.
  intros t1 t2 t3 H12.
  gdep t3.
  induction H12; intros t3 H23; inv H23; econstructor; unfold match_events13; eauto.
Qed.

Hypothesis bws12 : backward_simulation step1 step2
                                       match_states12 match_events12 observe1 observe2.

Hypothesis bws23 : backward_simulation step2 step3
                                       match_states23 match_events23 observe2 observe3.

Lemma bws_composition : backward_simulation step1 step3
                                            match_states13 match_events13 observe1 observe3.
Proof.
  intros s11 s31 t3 s32 [s21 [H12 H23]] Hexec3.
  exploit bws23; eauto.
  intros H.
  destruct H as [? [? [? ?]]].
  exploit bws12; eauto.
  intros H'.
  destruct H' as [? [? [? ?]]].
  eauto using match_events_composition.
Qed.

End Composition.
