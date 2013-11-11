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

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}.

Variable cblock : FaultRoutine.block.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.

Variable ctable_impl : list CSysCallImpl.

Let faultHandler := FaultRoutine.faultHandler _ QuasiAbstractMachine.fetch_rule.
Let ctable := build_syscall_table (Z.of_nat (length faultHandler)) ctable_impl.

Context {WFCLatt: WfConcreteLattice cblock ctable T Latt CLatt}.

Variable atable : ASysTable T.
Hypothesis Hatable : parametric_asystable atable.
Hypothesis Hctable_impl_correct : ctable_impl_correct cblock atable ctable_impl faultHandler.
Hypothesis table_syscall_lowstep : forall o, syscall_lowstep o atable.
Hypothesis table_systable_inv : systable_inv atable.

Inductive concrete_i_equiv (o : T) :
  concrete_init_data -> concrete_init_data -> Prop :=
  | ci_equiv : forall ai1 ai2 ci1 ci2
                      (EQ : abstract_i_equiv o ai1 ai2)
                      (MATCH1 : ac_match_initial_data cblock QuasiAbstractMachine.fetch_rule ai1 ci1)
                      (MATCH2 : ac_match_initial_data cblock QuasiAbstractMachine.fetch_rule ai2 ci2),
                 concrete_i_equiv o ci1 ci2.

Instance CMObservation : TINI.Observation (tini_concrete_machine cblock ctable_impl) (Event T) := {
  out e := match e with
             | CEInt (z, t) m => EInt (z, valToLab t m)
           end;
  e_low := fun o e => @TINI.e_low _ _ (AMObservation atable) o e;
  e_low_dec := fun o e => TINI.e_low_dec o e;
  i_equiv := concrete_i_equiv
}.

Lemma ac_low_compatible :
  forall (o : T)
         (e1 : event (abstract_machine atable))
         (e2 : CEvent),
    ref_match_events (@abstract_concrete_ref _ _ _ cblock stamp_cblock
                                             ctable_impl
                                             WFCLatt
                                             atable Hatable Hctable_impl_correct) e1 e2 ->
    (TINI.e_low o (TINI.out e1)
       <-> TINI.e_low o (@TINI.out _ _ CMObservation e2)).
Proof.
  simpl.
  intros o [[x xl]] [[x' xt] m] H; simpl.
  inv H. unfold pcatom_labToVal in ATOMS. simpl in ATOMS.
  destruct ATOMS as [? TAG]. subst x'.
  assert (valToLab xt m = xl) by (eapply labToVal_valToLab_id; eauto).
  subst. reflexivity.
Qed.

Lemma concrete_equiv_abstract_equiv :
  forall o ci1 ci2,
    concrete_i_equiv o ci1 ci2 ->
    exists ai1 ai2,
      abstract_i_equiv o ai1 ai2 /\
      ac_match_initial_data cblock QuasiAbstractMachine.fetch_rule ai1 ci1 /\
      ac_match_initial_data cblock QuasiAbstractMachine.fetch_rule ai2 ci2.
Proof.
  intros o ci1 ci2 EQ.
  inv EQ. eauto.
Qed.

Lemma ac_match_events_equiv :
  forall o e11 e12 e21 e22
         (EQ : @TINI.a_equiv (abstract_machine atable) _ _ o (E e11) (E e12))
         (MATCH1 : ref_match_events (abstract_concrete_ref stamp_cblock Hatable Hctable_impl_correct) e11 e21)
         (MATCH2 : ref_match_events (abstract_concrete_ref stamp_cblock Hatable Hctable_impl_correct) e12 e22),
    @TINI.a_equiv (tini_concrete_machine cblock ctable_impl) _ _ o (E e21) (E e22).
Proof.
  simpl.
  intros o [[x1 xl1]] [[x2 xl2]] [[x1' xt1] m1] [[x2' xt2] m2].
  intros.
  inv EQ; inv MATCH1; inv MATCH2;
  repeat match goal with
           | ATOMS : pcatom_labToVal _ _ _ |- _ =>
             unfold pcatom_labToVal in ATOMS;
             simpl in ATOMS; destruct ATOMS; subst
           | H : TINI.out _ = TINI.out _ |- _ =>
             simpl in H; inv H
           | H : TINI.e_low _ _ |- _ =>
             simpl in H
         end;
  intuition; repeat subst;
  constructor (solve [simpl; eauto;
                      repeat match goal with
                               | H : labToVal _ _ _ |- _ =>
                                 eapply labToVal_valToLab_id in H; eauto; rewrite H
                             end;
                      eauto]).
Qed.

Lemma ac_tini_preservation_premises :
  tini_preservation_hypothesis
    (abstract_concrete_ref stamp_cblock Hatable Hctable_impl_correct).
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
          (abstract_machine atable) (tini_concrete_machine cblock ctable_impl)
          _ _ _
          (abstract_concrete_ref stamp_cblock Hatable Hctable_impl_correct)
          (abstract_noninterference_short table_syscall_lowstep table_systable_inv)
          ac_tini_preservation_premises).
Qed.

End NI.
