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
Require Import SOPCLattice.
Require TINI.

Open Scope Z_scope.

Set Implicit Arguments.


Section NI.

Definition tini_sop_fault_handler := sop_fault_handler QuasiAbstractMachine.fetch_rule.

Instance SOPwf' : WfConcreteLattice 
                    Zset.t
                    ZsetLat 
                    SOPClatt
                    (SOPSysTable tini_sop_fault_handler) := (SOPwf tini_sop_fault_handler).

Inductive concrete_i_equiv o :
  init_data tini_concrete_machine -> init_data tini_concrete_machine -> Prop :=
  | ci_equiv : forall p n s1 s2,
                 low_equiv_list (low_equiv_atom o)
                                (sop_am_init_stack s1)
                                (sop_am_init_stack s2) ->
                 concrete_i_equiv o
                   (p, s1, n)
                   (p, s2, n).

Instance CMObservation : TINI.Observation tini_concrete_machine Event := {
  out e :=  match e with
    | CEInt ca m => EInt (atom_ZToLab ca m)
  end;
  e_low := fun o e => TINI.e_low o e;
  e_low_dec := fun o e => TINI.e_low_dec o e;
  i_equiv := concrete_i_equiv
}.
Grab Existential Variables.
exact (SOPSysTable tini_sop_fault_handler).
Defined.

Lemma ac_low_compatible :
  forall o e1 e2,
    ref_match_events abstract_concrete_ref e1 e2 ->
    (TINI.e_low o (TINI.out e1)
       <-> TINI.e_low o (TINI.out e2)).
Proof.
  simpl.
  intros o [a1] [a2] H; simpl.
  inv H.
  erewrite atom_labToZ_ZToLab_id; eauto. 
  inv MATCH; eauto. 
  reflexivity.
Qed.

Lemma concrete_equiv_abstract_equiv :
  forall o ci1 ci2,
    concrete_i_equiv o ci1 ci2 ->
    exists ai1 ai2,
      abstract_i_equiv o ai1 ai2 /\
      ac_match_initial_data ai1 ci1 /\
      ac_match_initial_data ai2 ci2.
Proof.
  intros o [[p1 d1] n1] [[p2 d2] n2] H.
  inv H.
  exists (p2,sop_am_init_stack d1,n2,bot).
  exists (p2,sop_am_init_stack d2,n2,bot).
  repeat split; simpl; eauto.
Qed.

Lemma ac_match_events_equiv : forall o e11 e12 e21 e22,
   @TINI.a_equiv (abstract_machine (SOPSysTable tini_sop_fault_handler)) _ _ o (E e11) (E e12) ->
   ref_match_events abstract_concrete_ref e11 e21 ->
   ref_match_events abstract_concrete_ref e12 e22 ->
   @TINI.a_equiv tini_concrete_machine _ _ o (E e21) (E e22).
Proof.
  intros.
  destruct e11; destruct e12; simpl in *.
  subst.
  inv H.
  - simpl in *.
    inv H4. inv H1. inv H0.
    apply atom_labToZ_ZToLab_id in MATCH. 
    apply atom_labToZ_ZToLab_id in MATCH0.
    constructor; simpl; congruence.
  - inv H0. inv H1. 
    apply atom_labToZ_ZToLab_id in MATCH. 
    apply atom_labToZ_ZToLab_id in MATCH0.
    apply TINI.ee_high; simpl in *; congruence.
Qed.

Lemma ac_tini_preservation_premises :
  tini_preservation_hypothesis abstract_concrete_ref.
Proof.
  intros o. exists o.
  split. { apply ac_low_compatible. }
  split. { apply concrete_equiv_abstract_equiv. }
  apply ac_match_events_equiv.
Qed.

(* Here we prove that joinP satisfies the lowstep unwinding lemma *)
(* Could probably be shorten a lot... *)
Lemma SOP_lowstep : forall o : Zset.t, syscall_lowstep o (SOPSysTable tini_sop_fault_handler).
Proof.
  intros o id sys_info Hs.
  unfold SOPSysTable in Hs.
  destruct id; inv Hs.
  simpl.
  intros args1 args2 res1 res2 H H0 H1.
  destruct args1; destruct args2; inv H; try congruence.
  destruct a; destruct a0.
  destruct args1; destruct args2; inv H7; try congruence.
  destruct a; destruct a0.
  destruct args1; destruct args2; inv H8; try congruence.
  inv H0; inv H1.
  inv H5; inv H4.
  assert (forall b1 b2, (b2 = true -> b1 = true) -> (b1 = false -> b2 = false))
    by (destruct b1; destruct b2; intuition congruence).
  inv LEa.
  - inv LEa0.
    + destruct (Zset.add z2 (Zset.union t2 t0) <: o) eqn:E;
      constructor (assumption).
    + constructor; auto.
      * assert (Zset.union t1 t0 <: o = false). 
          apply (not_flows_not_join_flows_left (L:=ZsetLat)); auto.
        revert H0; apply H; intros.
        apply flows_trans with (2:=H0).
        apply Zset_add_incl.
      * assert (Zset.union t2 t0 <: o = false).
          apply (not_flows_not_join_flows_left (L:=ZsetLat)); auto.
        revert H0; apply H; intros.
        apply flows_trans with (2:=H0).
        apply Zset_add_incl.
  - constructor.
    + revert H3; apply H.
      intro T; apply flows_trans with (2:=T).
      eapply flows_trans; [idtac|apply Zset_add_incl].
      apply (@flows_join_left _ ZsetLat); auto.
    + revert H5; apply H.
      intro T; apply flows_trans with (2:=T).
      eapply flows_trans; [idtac|apply Zset_add_incl].
      apply (@flows_join_left _ ZsetLat); auto.
Qed.  

Lemma concrete_noninterference :
  TINI.tini CMObservation.
Proof.
   exact (@refinement_preserves_noninterference
          (abstract_machine (SOPSysTable tini_sop_fault_handler)) tini_concrete_machine
          _ _ _
          abstract_concrete_ref
          (abstract_noninterference SOP_lowstep)
          ac_tini_preservation_premises).
Qed.

End NI.
