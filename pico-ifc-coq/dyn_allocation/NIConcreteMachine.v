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

Instance CMObservation : TINI.Observation (tini_concrete_machine cblock) (Event observer) := {
  out e := abstract_event e;
  e_low := fun o e => TINI.e_low o e;
  e_low_dec := fun o e => TINI.e_low_dec o e;
  i_equiv := concrete_i_equiv
}.

Lemma ac_low_compatible :
  forall o e1 e2,
    ref_match_events (abstract_concrete_ref stamp_cblock) e1 e2 ->
    (TINI.e_low o (TINI.out e1)
       <-> TINI.e_low o (TINI.out e2)).
Proof.
  simpl.
  intros o [a1] [a2] H; simpl.
  inv H.
  erewrite <- atom_ZToLab_labToZ_id; eauto; reflexivity.
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

Lemma ac_match_events_equiv :
  forall o e11 e12 e21 e22
         (EQ : @TINI.a_equiv abstract_machine _ _ o (E e11) (E e12))
         (MATCH1 : ref_match_events (abstract_concrete_ref stamp_cblock) e11 e21)
         (MATCH2 : ref_match_events (abstract_concrete_ref stamp_cblock) e12 e22),
    @TINI.a_equiv (tini_concrete_machine cblock) _ _ o (E e21) (E e22).
Proof.
  simpl.
  intros.
  inv EQ; inv MATCH1; inv MATCH2;
  simpl in *; subst;
  constructor (solve [simpl in *; auto;
                          try rewrite (abstract_event_concretize_event (cblock := cblock)); eauto]).
Qed.

Lemma ac_tini_preservation_premises :
  tini_preservation_hypothesis (abstract_concrete_ref stamp_cblock).
Proof.
  intros o. exists o.
  split. { apply ac_low_compatible. }
  split. { apply concrete_equiv_abstract_equiv. }
  apply ac_match_events_equiv.
Qed.

Lemma concrete_noninterference :
  TINI.tini CMObservation.
Proof.
   exact (@refinement_preserves_noninterference
          abstract_machine (tini_concrete_machine cblock)
          _ _ _
          (abstract_concrete_ref stamp_cblock)
          abstract_noninterference
          ac_tini_preservation_premises).
Qed.

End NI.

(* DD: We stick with the "implicit types" formulation of the theorem, but
       you can print it fully using:
Set Printing All.
Check @concrete_noninterference.
*)
