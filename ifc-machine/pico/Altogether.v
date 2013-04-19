(* Std libs *)
Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.

(* Our libs *)
Require Import Utils.
Require Import Lattices.
Require Import CLattices.

(* Def of NI *)
Require Import LNIwithEvents.

(* Abstract Machine *)
Require Import TMUInstr.
Require Import Abstract Rules AbstractMachine.
Require Import AbstractObsEquiv NIAbstractMachine.

(* Concrete Machine *)
Require Import Concrete ConcreteMachineSmallStep CodeGen.
Require Import FaultRoutine.

Require Import Refinement.

Set Implicit Arguments.
Local Open Scope Z_scope. 
(** This file summarizes the results we already have and the one we aim at *)

Section Altogether.

(** * Abstract Machine *)
Context {L: Type} {Latt: JoinSemiLattice L}.

(** Initial state of the abstract machine *)
Variable mty : list (@Atom L) -> Prop.

Inductive initial_astate (P: list Instr) : @AS L -> Prop :=
| init_as: forall m, 
             mty m ->
             initial_astate P (AState m P nil (0,bot)).

(** * Non-interference property on the abstract Machine *)

(** Defining observation, execution traces, and indistingability relation *)
Let low_equiv_prog := fun (o:L) => low_equiv_list (low_equiv_instr o).
Let observe_astate : @AS L -> @AS L := (fun x => x).
Let aexec_with_trace := sys_trace step_rules success observe_astate.
Let indistinguishable := lockstep_indist low_pc success low_equiv_full_state.

Theorem NI_abstract_machine: forall o s s' P P' T T', 
    low_equiv_prog o P P' ->
    initial_astate P s ->
    initial_astate P' s'->
    aexec_with_trace s T ->
    aexec_with_trace s' T' ->
    indistinguishable o T T'.
Proof.
  admit. (* TODO with lockstep_ni_amach *)
Qed.

(** * Concrete Machine *)
Context {CLatt: ConcreteLattice L}.

(** The fault handler code *)
Definition faultHandler := FaultRoutine.faultHandler (fun opcode => existT _ (labelCount opcode) (fetch_rule opcode)).
Variable mtyCache : list (@Atom Z).

(** Initial state of the concrete machine *)
Inductive initial_cstate (P: list Instr) : CS -> Prop :=
| init_cs : forall m, initial_cstate P (CState mtyCache m faultHandler P nil (0,labToZ bot) false).

(* Now defined in Refinement ...
(** Aux functions yet to be defined *)
Variable c_to_a_stack : list CStkElmt -> list (@StkElmt L). 

Variable c_to_a_mem : list (@Atom L) -> list (@Atom Z).

(** Observing a concete cache is just projecting it a the abstract level *)
Let observe_cstate (cs: CS) : @AS L := 
  match cs with 
    | CState c m fh i s pc p => AState (c_to_a_mem m) i (c_to_a_stack s) (ZToLab pc)
  end.
  
*)

Let cexec_with_trace := sys_trace cstep c_success observe_cstate.

Theorem NI_concrete_machine: forall o P P' s s' T T', 
    initial_cstate P s -> 
    initial_cstate P' s' ->
    low_equiv_prog o P P' ->
    cexec_with_trace s T ->
    cexec_with_trace s' T' ->
    indistinguishable o T T'.
Proof.
  admit. (* TODO with refinement + NI preservation *)
Qed.

End Altogether.



  
