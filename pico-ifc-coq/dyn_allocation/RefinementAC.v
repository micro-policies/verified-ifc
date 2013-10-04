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

Definition tini_match_states := match_states cblock QuasiAbstractMachine.fetch_rule.

Definition tini_concrete_machine := concrete_machine cblock faultHandler ctable_impl.

Program Definition abstract_concrete_ref :
  refinement (abstract_machine atable) tini_concrete_machine :=
  @ref_composition _ _ _
                   (abstract_quasi_abstract_ref Hatable)
                   (quasi_abstract_concrete_ref stamp_cblock
                                                (handler_correct_succeed _ _ _ _ _)
                                                (handler_correct_fail _ _ _ _ _)
                                                Hctable_impl_correct)
                   (@ac_match_initial_data _ _ _ cblock fetch_rule)
                   match_events
                   _ _.
Next Obligation.
  eauto.
Qed.

End Refinement.
