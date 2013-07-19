(* The concrete machine enjoys TINI. *)

Require Import List.
Require Import ZArith.

Require Import Utils.
Require Import Lattices.
Require Import CLattices.
Require Import Instr.
Require Import AbstractCommon.
Require Import AbstractMachine.
Require Import NIAbstractMachine.
Require Import Concrete.
Require Import ConcreteMachine.
Require Import ConcreteExecutions.
Require Import Semantics.
Require Import Refinement.
Require Import RefinementAC.
Require TINI.

Open Scope Z_scope.

Set Implicit Arguments.


Section NI.

Context {observer: Type}
        {Latt: JoinSemiLattice observer}
        {CLatt: ConcreteLattice observer}
        {WFCLatt: WfConcreteLattice observer Latt CLatt}.

Inductive concrete_i_equiv (o : observer) :
  init_data tini_concrete_machine -> init_data tini_concrete_machine -> Prop :=
  | ci_equiv : forall p n l s1 s2,
                 low_equiv_list (low_equiv_atom o) s1 s2 ->
                 concrete_i_equiv o
                   (p, (mem_labToZ s1), n, (labToZ l))
                   (p, (mem_labToZ s2), n, (labToZ l)).

Definition abstract_event' {L} (CLatt : ConcreteLattice L) (ce : CEvent) :=
  match ce with
    | CEInt ca => EInt (atom_ZToLab ca)
  end.

Instance CMObservation : TINI.Observation tini_concrete_machine := {
  e_low := fun o e => TINI.e_low o (abstract_event' _ e);
  e_low_dec := fun o e => TINI.e_low_dec o (abstract_event' _ e);
  i_equiv := concrete_i_equiv
}.

Lemma ac_low_compatible :
  forall o e1 e2,
    ref_match_events abstract_concrete_ref e1 e2 ->
    (TINI.e_low o e1 <-> TINI.e_low (S:=tini_concrete_machine) o e2).
Proof.
  simpl.
  intros o [a1] [a2] H; simpl.
  inv H.
  rewrite <- atom_ZToLab_labToZ_id.
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
  intros o [[[p1 d1] n1] z1] [[[p2 d2] n2] z2] H.
  inv H.
  exists (p2,s1,n2,l).
  exists (p2,s2,n2,l).
  repeat split; simpl; eauto.
Qed.

Lemma ac_match_events_equiv : forall o e11 e12 e21 e22,
                                @TINI.a_equiv abstract_machine _ o (E e11) (E e12) ->
                                ref_match_events abstract_concrete_ref e11 e21 ->
                                ref_match_events abstract_concrete_ref e12 e22 ->
                                @TINI.a_equiv tini_concrete_machine _ o (E e21) (E e22).
Proof.
  unfold match_events.
  intros.
  destruct e11; destruct e12; simpl in *.
  subst.
  inv H; constructor; simpl in *.
  generalize (abstract_action_concretize_action (E (EInt a))); simpl; congruence.
  generalize (abstract_action_concretize_action (E (EInt a0))); simpl; congruence.
Qed.

Lemma ac_tini_preservation_premises :
  tini_preservation_hypothesis abstract_concrete_ref.
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
          abstract_machine tini_concrete_machine
          _ _
          abstract_concrete_ref
          abstract_noninterference
          ac_tini_preservation_premises).
Qed.

End NI.

(* DD: We stick with the "implicit types" formulation of the theorem, but
       you can print it fully using:
Set Printing All.
Check @concrete_noninterference.
*)
