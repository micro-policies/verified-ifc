Require Import List.
Require Import ZArith.

Require Import Utils.
Require Import Lattices.
Require Import CLattices.
Require Import WfCLattices.
Require Import TMUInstr.
Require Import Abstract.
Require Import AbstractCommon.
Require Import AbstractMachine.
Require Import AbstractObsEquiv.
Require Import NIAbstractMachine.
Require Import Concrete.
Require Import ConcreteMachineSmallStep.
Require Import Determinism.
Require Import Refinement.
Require Import CExec.
Require Import BackwardCacheHit.
Require Import Backward.
Require Import Ref.
Require Import AbstractSimulation.
Require TINI.

Open Scope Z_scope.

Set Implicit Arguments.

Section NI.

Context {L: Type}
        {Latt: JoinSemiLattice L}
        {CLatt: ConcreteLattice L}
        {WFCLatt: WfConcreteLattice L Latt CLatt}.

Section Observation.

Context {E : Type} `{TINI.ObservableEvent L (option E)}.

Hypothesis none_high : forall o, ~ TINI.e_low o None.

Lemma remove_none_observe :
  forall o t,
    TINI.observe o (remove_none t) =
    TINI.observe o t.
Proof.
  induction t as [|e t IH]; simpl; auto.
  destruct e as [e|]; simpl; auto.
  - destruct (TINI.e_low_dec o (Some e)); trivial.
    rewrite IH. trivial.
  - destruct (TINI.e_low_dec o None); trivial.
    exfalso.
    eapply none_high.
    eauto.
Qed.

End Observation.

Instance CMObservableEvent : TINI.ObservableEvent L (option CEvent) := {
  e_equiv := fun o e1 e2 =>
               low_equiv_event o (abstract_event e1) (abstract_event e2);
  e_low := fun o e => TINI.e_low o (abstract_event e);
  e_low_dec := fun o e => TINI.e_low_dec o (abstract_event e);
  e_equiv_low := fun o e1 e2 =>
                   TINI.e_equiv_low (ObservableEvent := AMObservableEvent)
                                    o (abstract_event e1) (abstract_event e2);
  e_high_e_equiv := fun o e1 e2 =>
                      TINI.e_high_e_equiv o (abstract_event e1) (abstract_event e2)
}.

Definition concrete_initial_data :=
  (list (@Atom Z) * list Instr)%type.

Definition concrete_i_equiv (o : L) (i1 i2 : concrete_initial_data) :=
  snd i1 = snd i2 /\
  exists m1 m2,
    fst i1 = mem_labToZ m1 /\
    fst i2 = mem_labToZ m2 /\
    low_equiv_list (low_equiv_atom o) m1 m2.

Definition concrete_initial_state (i : concrete_initial_data) :=
  {| cache := nil;
     mem := fst i;
     fhdl := faultHandler;
     imem := snd i;
     stk := nil;
     pc := (0, labToZ bot);
     priv := false |}.

Definition ac_match_initial_data (ai : abstract_initial_data)
                                 (ci : concrete_initial_data) :=
  mem_labToZ (fst ai) = fst ci /\
  snd ai = snd ci.

Lemma filter_cons_inv_strong :
  forall X (l1 : list X) x2 l2
         (f : X -> bool),
    x2 :: l2 = filter f l1 ->
    exists l11 l12,
      l1 = l11 ++ l12 /\
      filter f l11 = x2 :: nil /\
      filter f l12 = l2.
Proof.
  intros X l1.
  induction l1 as [|x1 l1 IH]; simpl; try congruence.
  intros.
  destruct (f x1) eqn:E.
  - exists (x1 :: nil).
    exists l1.
    simpl.
    rewrite E.
    inv H.
    eauto.
  - exploit IH; eauto.
    clear IH.
    intros [l11 [l12 [H1 [H2 H3]]]].
    subst.
    exists (x1 :: l11).
    exists l12.
    simpl.
    rewrite E. eauto.
Qed.

Lemma filter_app :
  forall X (l1 l2 : list X) (f : X -> bool),
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1 as [|x l1 IH]; simpl; intros. trivial.
  rewrite IH. destruct (f x); auto.
Qed.

Lemma ac_observations_compatible :
  forall o,
    observations_compatible match_events
                            (@remove_none (@Event _)) (TINI.observe o)
                            (@remove_none CEvent) (TINI.observe o).
Proof.
  intros o t1 t2 H.
  remember (remove_none t2) as t2'. gdep t2.
  remember (remove_none t1) as t1'. gdep t1.
  induction H as [|e1' t1' e2' t2' H MATCH IH];
  intros t1 H1 t2 H2;
  simpl in *.
  - rewrite <- remove_none_observe;
    try solve [intros o' H; inv H].
    rewrite <- H1. simpl.
    rewrite <- remove_none_observe;
    try solve [intros o' H; inv H].
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
    assert (E : TINI.observe o (t11 ++ t12) =
                TINI.observe o t11 ++ TINI.observe o t12) by
        apply filter_app.
    rewrite E. clear E.
    assert (E : TINI.observe o (t21 ++ t22) =
                TINI.observe o t21 ++ TINI.observe o t22) by
        apply filter_app.
    rewrite E. clear E.
    rewrite <- remove_none_observe;
    try solve [intros o' H'; inv H'].
    unfold remove_none.
    rewrite H12.
    assert (EQ : TINI.observe o t21 = TINI.observe o (e2' :: nil)).
    { rewrite <- remove_none_observe;
      try solve [intros o' H'; inv H'].
      unfold remove_none.
      rewrite H22. reflexivity. }
    rewrite EQ. clear EQ. simpl.
    unfold match_events in *.
    subst.
    destruct (visible_event_dec o (abstract_event e2')); simpl; trivial.
    constructor; trivial.
Qed.

Lemma concrete_equiv_abstract_equiv :
  forall o ci1 ci2,
    concrete_i_equiv o ci1 ci2 ->
    exists ai1 ai2,
      abstract_i_equiv o ai1 ai2 /\
      ac_match_initial_data ai1 ci1 /\
      ac_match_initial_data ai2 ci2.
Proof.
  intros o [cm1 ?] [cm2 p] [? [am1 [am2 [? [? ?]]]]].
  simpl in *.
  subst.
  exists (am1, p). exists (am2, p).
  eauto.
  repeat split; simpl; eauto.
Qed.

Lemma ac_match_initial_data_match_initial_states :
  forall ai ci,
    ac_match_initial_data ai ci ->
    match_states (abstract_initial_state ai)
                 (concrete_initial_state ci).
Proof.
  intros [am ?] [cm p] [H1 H2].
  simpl in *.
  subst.
  constructor; simpl; eauto.
  - intros op vls pcl contra.
    inv contra.
    inv TAG1.
    inv H.
  - constructor.
Qed.

Lemma ac_match_events_equiv : forall o e11 e12 e21 e22,
                                TINI.e_equiv o e11 e12 ->
                                match_events e11 e21 ->
                                match_events e12 e22 ->
                                TINI.e_equiv o e21 e22.
Proof.
  unfold match_events.
  intros.
  subst.
  exact H.
Qed.

Lemma noninterference : TINI.tini concrete_initial_state cstep concrete_i_equiv.
Proof.
Admitted.

End NI.
