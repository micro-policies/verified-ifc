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
Require Import NIConcreteMachine.
Require Import SOPCLattice.
Require Import SOPSysCalls.

Open Scope Z_scope.

Set Implicit Arguments.

Section NI.

Variable cblock : FaultRoutine.block.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.

Lemma sop_noninterference : TINI.tini (CMObservation (Latt := ZsetLat)
                                                     (CLatt := SOPClatt cblock)
                                                     cblock
                                                     SOPCSysTable SOPASysTable).
Proof.
  eapply concrete_noninterference; eauto.
  - eapply SOPwf; eauto. constructor.
  - eapply sop_asystable_parametric.
  - apply sop_syscall_impls_correct; eauto.
  - eapply sop_asystable_lowstep.
  - eapply sop_asystable_inv.
Qed.

End NI.
