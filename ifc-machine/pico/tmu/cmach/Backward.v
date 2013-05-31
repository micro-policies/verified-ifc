Require Import List.
Require Import ZArith.

Require Import Utils.
Require Import Lattices.
Require Import CLattices.
Require Import WfCLattices.
Require Import TMUInstr.
Require Import Abstract.
Require Import AbstractCommon.
Require Import Rules.
Require AbstractMachine.
Require QuasiAbstractMachine.
Require Import Concrete.
Require Import ConcreteMachineSmallStep.
Require Import Determinism.
Require Import Refinement.
Require Import CExec.
Require Import BackwardCacheMiss.
Require Import BackwardCacheHit.
Require Import Ref.
Require Import AbstractSimulation.

Open Scope Z_scope.

Set Implicit Arguments.

Section Backward.

Context {L: Type}
        {Latt: JoinSemiLattice L}
        {CLatt: ConcreteLattice L}
        {WFCLatt: WfConcreteLattice L Latt CLatt}.

Definition match_events e1 e2 :=
  e1 = abstract_event e2.

Definition remove_none {T} (l : list (option T)) :=
  filter (@is_some _) l.

Lemma filter_cons_inv :
  forall A (f : A -> bool) a l1 l2,
    a :: l1 = filter f l2 ->
    exists l2', l1 = filter f l2'.
Proof.
  induction l2 as [|a' l2 IH]; simpl. congruence.
  destruct (f a'); intros H; auto.
  inv H. eauto.
Qed.

Lemma quasi_abstract_concrete_bwdsim :
  backward_simulation QuasiAbstractMachine.step_rules cstep match_states match_events
                      remove_none remove_none.
Proof.
  intros s1 s2 t2 s2' MATCH EXEC.
  apply exec_cexec in EXEC.
  match type of EXEC with
    | cexec _ ?T _ =>
      remember T as t2'
  end.
  gdep t2. gdep s1.
  unfold remove_none.
  induction EXEC; intros s1 MATCH t2 Ht2; unfold remove_none.
  - exists nil. exists s1.
    split. constructor.
    rewrite <- Ht2. constructor.
  - inv MATCH.
    apply kernel_run_until_user_l in H.
    inv H.
  - exploit cache_hit_simulation; eauto.
    intros [s1' [STEP MATCH']].
    assert (exists t', t = filter (@is_some _) t') by
        (destruct e; eauto using filter_cons_inv).
    inv H2.
    exploit IHEXEC; eauto.
    intros [? [? [? ?]]].
    eexists. eexists.
    split. econstructor 2; eauto.
    rewrite <- Ht2.
    destruct e as [[[? ?]]|]; simpl; eauto.
    constructor; auto.
    reflexivity.
  - exploit cache_miss_simulation; eauto.
Qed.

Lemma abstract_concrete_bwdsim :
  backward_simulation AbstractMachine.step_rules cstep match_states match_events
                      remove_none remove_none.
Proof.
  eapply bws_composition with (state2 := AS)
                              (step2 := QuasiAbstractMachine.step_rules)
                              (observe2 := remove_none)
                              (match_states12 := eq)
                              (match_events12 := eq)
                              (match_events23 := match_events);
  eauto; intros; subst; trivial.
  - refine (weaken_backward_simulation _ abstract_quasi_abstract_bwdsim).
    induction 1. constructor.
    subst.
    simpl. destruct (is_some e2); trivial.
    constructor; trivial.
  - exact quasi_abstract_concrete_bwdsim.
Qed.

End Backward.
