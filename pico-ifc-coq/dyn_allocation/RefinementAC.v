Require Import EquivDec.
Require Import List.
Require Import ZArith.

Require Import Utils.
Require Import Lattices.
Require Import CLattices.

(* For labsToZs, should be possible to factor that into another file *)
Require Import FaultRoutine.

Require Import Semantics.
Require Import Instr.
Require Import AbstractCommon.
Require Import Rules.
Require Import Memory.
Require Import AbstractMachine.
Require Import QuasiAbstractMachine.
Require Import Concrete.
Require Import ConcreteExecutions.
Require Import ConcreteMachine.
Require Import Refinement.
Require Import RefinementAQA.
Require Import RefinementQAC.

Open Scope list_scope.

Set Implicit Arguments.

Section Refinement.

Variable cblock : FaultRoutine.block.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}
        {WFCLatt: WfConcreteLattice cblock T Latt CLatt}.

Definition tini_fetch_rule_withsig :=
  (fun opcode => existT _
                        (QuasiAbstractMachine.labelCount opcode)
                        (QuasiAbstractMachine.fetch_rule opcode)).
Definition tini_faultHandler := FaultRoutine.faultHandler tini_fetch_rule_withsig.
Definition tini_match_states := match_states cblock QuasiAbstractMachine.fetch_rule.

Definition tini_concrete_machine := concrete_machine cblock tini_faultHandler.

Program Definition weak_abstract_quasi_abstract_ref :
  refinement abstract_machine tini_quasi_abstract_machine :=
  @weaken_refinement _ _
                     abstract_quasi_abstract_ref
                     remove_none remove_none _.

Next Obligation.
  unfold observations_compatible. simpl.
  induction 1.
  - constructor.
  - subst.
    simpl. destruct (is_some e2); trivial.
    constructor; trivial.
Qed.

Program Definition abstract_concrete_ref :
  refinement abstract_machine tini_concrete_machine :=
  @ref_composition _ _ _
                   weak_abstract_quasi_abstract_ref
                   (quasi_abstract_concrete_ref stamp_cblock fetch_rule)
                   (@ac_match_initial_data _ _ _ fetch_rule)
                   match_events
                   _ _ _.

Next Obligation.
  eauto.
Qed.

End Refinement.
