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
Require Import RefinementAQA.
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

Variable table : forall S, ASysTable observer S.
Hypothesis table_param : match_asystables (table observer) (table unit).
Hypothesis table_syscall_lowstep : forall o, syscall_lowstep o (table observer).
Hypothesis table_systable_inv : systable_inv (table observer).

Inductive concrete_i_equiv (o : observer) :
  init_data (tini_concrete_machine cblock) -> init_data (tini_concrete_machine cblock) -> Prop :=
  | ci_equiv : forall ai1 ai2 ci1 ci2
                      (EQ : abstract_i_equiv o ai1 ai2)
                      (MATCH1 : ac_match_initial_data ai1 ci1)
                      (MATCH2 : ac_match_initial_data ai2 ci2),
                 concrete_i_equiv o ci1 ci2.

Instance CMObservation : TINI.Observation (tini_concrete_machine cblock) (Event observer) := {
  out e := match e with
             | CEInt (z, t) m => EInt (z, valToLab t m)
           end;
  e_low := fun o e => @TINI.e_low _ _ (AMObservation (table observer)) o e;
  e_low_dec := fun o e => TINI.e_low_dec o e;
  i_equiv := concrete_i_equiv
}.

Lemma ac_low_compatible :
  forall (o : observer)
         (e1 : event (abstract_machine (table observer)))
         (e2 : event (tini_concrete_machine cblock)),
    ref_match_events (@abstract_concrete_ref cblock stamp_cblock
                                             observer Latt CLatt WFCLatt
                                             (table observer) (table unit) table_param) e1 e2 ->
    (TINI.e_low o (TINI.out e1)
       <-> TINI.e_low o (@TINI.out _ _ CMObservation e2)).
Proof.
  simpl.
  intros o [[x xl]] [[x' xt] m] H; simpl.
  inv H. unfold pcatom_labToVal in ATOMS. simpl in *.
  destruct ATOMS as [? TAG]. subst x'.
  assert (valToLab xt m = xl) by (eapply labToVal_valToLab_id; eauto).
  subst. reflexivity.
Qed.

Lemma concrete_equiv_abstract_equiv :
  forall o ci1 ci2,
    concrete_i_equiv o ci1 ci2 ->
    exists ai1 ai2,
      abstract_i_equiv o ai1 ai2 /\
      ac_match_initial_data ai1 ci1 /\
      ac_match_initial_data ai2 ci2.
Proof.
  intros o ci1 ci2 EQ.
  inv EQ. eauto.
Qed.

Lemma ac_match_events_equiv :
  forall o e11 e12 e21 e22
         (EQ : @TINI.a_equiv (abstract_machine (table observer)) _ _ o (E e11) (E e12))
         (MATCH1 : ref_match_events (abstract_concrete_ref stamp_cblock table_param) e11 e21)
         (MATCH2 : ref_match_events (abstract_concrete_ref stamp_cblock table_param) e12 e22),
    @TINI.a_equiv (tini_concrete_machine cblock) _ _ o (E e21) (E e22).
Proof.
  simpl.
  intros o [[x1 xl1]] [[x2 xl2]] [[x1' xt1] m1] [[x2' xt2] m2].
  intros.
  inv EQ; inv MATCH1; inv MATCH2;
  unfold pcatom_labToVal in *; simpl in *;
  try match goal with
        | H : EInt _ = EInt _ |- _ => inv H
      end;
  intuition; repeat subst;
  constructor (solve [simpl in *; eauto;
                      repeat match goal with
                               | H : labToVal _ _ _ |- _ =>
                                 eapply labToVal_valToLab_id in H; eauto; rewrite H
                             end;
                      eauto]).
Qed.

Lemma ac_tini_preservation_premises :
  tini_preservation_hypothesis (abstract_concrete_ref stamp_cblock table_param).
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
          (abstract_machine (table observer)) (tini_concrete_machine cblock)
          _ _ _
          (abstract_concrete_ref stamp_cblock table_param)
          (abstract_noninterference_short table_syscall_lowstep table_systable_inv)
          ac_tini_preservation_premises).
Qed.

End NI.

(* DD: We stick with the "implicit types" formulation of the theorem, but
       you can print it fully using:
Set Printing All.
Check @concrete_noninterference.
*)
