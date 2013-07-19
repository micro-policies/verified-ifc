Require Import List.
Require Import ZArith.

Require Import Utils.
Require Import Lattices.
Require Import CLattices.
Require Import Instr.
Require Import Memory.
Require Import AbstractCommon.
Require Import AbstractMachine.
Require Import NIAbstractMachine.
Require Import Concrete.
Require Import ConcreteMachine.
Require Import ConcreteExecutions.
Require Import Semantics.
Require Import Refinement.
Require Import RefinementQAC.
Require Import RefinementAC.
Require TINI.

Open Scope Z_scope.

Set Implicit Arguments.


Section NI.

Variable cblock : FaultRoutine.block.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.

Context {observer : Type}
        {Latt: JoinSemiLattice observer}
        {CLatt: ConcreteLattice observer}
        {WFCLatt: WfConcreteLattice cblock observer Latt CLatt}.

Inductive concrete_i_equiv (o : observer) :
  init_data (tini_concrete_machine cblock) -> init_data (tini_concrete_machine cblock) -> Prop :=
  | ci_equiv : forall p l s1 s2,
                 low_equiv_list (low_equiv_atom o) s1 s2 ->
                 concrete_i_equiv o
                   (p, (map pcatom_labToZ s1), labToZ l)
                   (p, (map pcatom_labToZ s2), labToZ l).

Instance CMObservation : TINI.Observation (tini_concrete_machine cblock) observer := {
  e_low := fun o e => TINI.e_low o (abstract_event e);
  e_low_dec := fun o e => TINI.e_low_dec o (abstract_event e);
  i_equiv := concrete_i_equiv
}.

Lemma ac_observations_compatible :
  forall o,
    observations_compatible (abstract_concrete_ref stamp_cblock)
                            (TINI.observe AMObservation o)
                            (TINI.observe CMObservation o).
Proof.
  unfold observations_compatible.
  eapply observations_compatible_option; simpl;
  try (intros o H; inv H).
  intros.
  inv H.
  rewrite (abstract_event_concretize_event (cblock := cblock)).
  intuition.
Qed.

Lemma concrete_equiv_abstract_equiv :
  forall o ci1 ci2,
    concrete_i_equiv o ci1 ci2 ->
    exists ai1 ai2,
      abstract_i_equiv o ai1 ai2 /\
      ac_match_initial_data ai1 ci1 /\
      ac_match_initial_data ai2 ci2.
Proof.
  intros o [[p1 d1] z1] [[p2 d2] z2] H.
  inv H.
  exists (p2,s1,l).
  exists (p2,s2,l).
  repeat split; simpl; eauto.
Qed.

Lemma ac_match_events_equiv : forall o e11 e12 e21 e22,
                                @TINI.e_equiv abstract_machine _ _ o e11 e12 ->
                                match_events e11 e21 ->
                                match_events e12 e22 ->
                                @TINI.e_equiv (tini_concrete_machine cblock) _ _ o e21 e22.
Proof.
  unfold match_events.
  intros.
  subst.
  inv H; constructor; auto; simpl;
  rewrite (abstract_event_concretize_event (cblock := cblock));
  auto.
Qed.

Lemma concrete_noninterference :
  TINI.tini CMObservation.
Proof.
   exact (@refinement_preserves_noninterference
          abstract_machine (tini_concrete_machine cblock)
          _ _ _
          (abstract_concrete_ref stamp_cblock)
          ac_observations_compatible
          abstract_noninterference
          concrete_equiv_abstract_equiv
          ac_match_events_equiv).
Qed.

End NI.

(* DD: We stick with the "implicit types" formulation of the theorem, but
       you can print it fully using:
Set Printing All.
Check @concrete_noninterference.
*)
