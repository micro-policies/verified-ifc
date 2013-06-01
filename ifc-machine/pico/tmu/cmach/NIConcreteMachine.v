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
Require Import BackwardCacheMiss.
Require Import BackwardCacheHit.
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

Lemma noninterference : TINI.tini concrete_initial_state cstep concrete_i_equiv.
Proof.
Admitted.

End NI.
