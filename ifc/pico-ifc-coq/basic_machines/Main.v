(** This file summarizes the main results in the development. *)

Require Coq.Unicode.Utf8.

Require Import TINI.
Require Import Lattices.
Require Import CLattices.
Require Import AbstractMachine.
Require Import QuasiAbstractMachine.
Require Import ConcreteMachine.
Require Import Refinement.
Require Import NIAbstractMachine.
Require Import RefinementCA.
Require Import RefinementAC.
Require Import NIConcreteMachine.
Require Import Encodable.

Section Main.

(** We consider some arbitrary type [T] equipped with a lattice
   structure [L]. [L] is implemented by the concrete lattice [CL], which
   is assumed to be a correct implementation, as denoted by [WF]. *)

Variable T : Type.
Variable L : JoinSemiLattice T.
Variable CL : ConcreteLattice T.
Variable EL : Encodable T.
Variable WF : WfConcreteLattice T L CL EL.

(** Some handy notations *)
Notation "s1 →* [ t ] s2" := (exec s1 t s2) (at level 60).
Notation "i1 ≈i [ o ] i2" := (i_equiv o i1 i2) (at level 60).
Notation "t1 ≈t t2" := (ti_trace_indist t1 t2) (at level 60).
Notation "ia ▷i ic" := (ac_match_initial_data ia ic) (at level 60).
Notation "ta ▷t tc" := (match_traces abstract_machine tini_concrete_machine
                                     match_events ta tc) (at level 60).
Notation "tc ◁t ta" := (match_traces tini_concrete_machine abstract_machine
                                     (fun e1 e2 => match_events e2 e1) tc ta) (at level 60).
Notation "tq ▷Rt tc" := (match_traces (quasi_abstract_machine _)
                                       (concrete_machine _)
                                       match_events tq tc) (at level 60).


(** The generic concrete machine refines the generic symbolic machine.
   The genericity lies here in the parameter [rule_table] that is used
   to define both machines 

   NB: The type of [rule_table] says that the symbolic rule uses
       only the right amount of label variables (the type is depending on
       the opcode)
*)

Theorem refinement_symbolic_concrete :
  forall (rule_table : forall o : Instr.OpCode, Rules.AllowModify (labelCount o))
         (iq : init_data (ifc_quasi_abstract_machine rule_table))
         (ic : init_data (concrete_machine (faultHandler rule_table)))
         (tc : list (event (concrete_machine (faultHandler rule_table))))
         (sc : state (concrete_machine (faultHandler rule_table))),
    iq ▷i ic ->
    init_state (concrete_machine (faultHandler rule_table)) ic →* [tc] sc ->
    exists (tq : list (event (ifc_quasi_abstract_machine rule_table)))
           (sq : state (ifc_quasi_abstract_machine rule_table)),
      init_state (ifc_quasi_abstract_machine rule_table) iq →* [tq] sq /\
      tq ▷Rt tc.
Proof. 
  intros. eapply (ref_prop (quasi_abstract_concrete_ref rule_table)) ; eauto. 
Qed.
    
(** The concrete machine running with the correct fault handler refines
   the abstract machine *)

Theorem refinement_abstract_concrete :
  forall (ia : init_data abstract_machine)
         (ic : init_data tini_concrete_machine)
         (tc : list (event tini_concrete_machine))
         (sc : state tini_concrete_machine),
    ia ▷i ic ->
    init_state tini_concrete_machine ic →* [tc] sc ->
    exists (ta : list (event abstract_machine))
           (sa : state abstract_machine),
      init_state abstract_machine ia →* [ta] sa /\
      ta ▷t tc.
Proof. intros. eapply (ref_prop abstract_concrete_ref); eauto. Qed.

(** The abstract machine refines the concrete machine running with the
   correct fault handler *)

Theorem refinement_concrete_abstract :
  forall (ic : init_data tini_concrete_machine)
         (ia : init_data abstract_machine)
         (ta : list (event abstract_machine))
         (sa : state abstract_machine),
    ia ▷i ic ->
    init_state abstract_machine ia →* [ta] sa ->
    exists (tc : list (event tini_concrete_machine))
           (sc : state tini_concrete_machine),
      init_state tini_concrete_machine ic →* [tc] sc /\
      tc ◁t ta.
Proof. intros. eapply (ref_prop concrete_abstract_ref); simpl; eauto. Qed.


(** Definition of Termination-insensitive noninterference (TINI) *)

Definition TINI (S:semantics) (O:Observation S) : Prop :=
  forall (o : observer (S:=S))
         (i1 i2 : init_data S)
         (t1 t2 : list (event S))
         (s1 s2 : state S),
    i1 ≈i [o] i2 ->
    init_state S i1 →* [t1] s1 ->
    init_state S i2 →* [t2] s2 ->
    observe O o t1 ≈t observe O o t2.


(** The abstract machine has TINI *)

Theorem ni_abstract_machine : TINI abstract_machine AMObservation.
Proof. unfold TINI. intros. eapply abstract_noninterference; eauto. Qed.



(** TINI is preserved by refinement ([S2] refines [S1], and some technical conditions (see paper's Section 10) *)
Theorem tini_preservation_by_refinement : 
  forall (S1 S2 : semantics) (O1 : Observation S1) (O2 : Observation S2)
    (match_i: init_data S1 -> init_data S2 -> Prop)
    (match_e: event S1 -> event S2 -> Prop),
  
    (forall i1 i2 t2 s2,
         match_i i1 i2 -> 
         (init_state S2 i2) →*[t2] s2 ->
         exists t1 s1,
           (init_state S1 i1) →*[t1] s1 /\ match_traces S1 S2 match_e t1 t2) ->

    (forall o2, exists o1,
       (forall e1 e2, match_e e1 e2 -> (e_low o1 e1 <-> e_low o2 e2))
       /\
       (forall i2 i2', i2 ≈i[o2] i2' -> 
                       exists i1 i1', 
                         i1 ≈i[o1] i1' /\ match_i i1 i2 /\ match_i i1' i2')
       /\
       (forall e1 e2 e1' e2',
          match_e e1 e2 ->
          match_e e1' e2' ->
          a_equiv O1 o1 (E e1) (E e1') -> 
          a_equiv O2 o2 (E e2) (E e2'))) ->

    TINI S1 O1 -> TINI S2 O2.
Proof. 
  unfold TINI; intros. 
  eapply (@refinement_preserves_noninterference S1 S2 O1 O2 (Build_refinement H)); eauto.
  unfold tini; eauto.
  intros o2. destruct (H0 o2) as (o1 & T1 & T2 & T3); eauto.
Qed.


(** The concrete_machine running with the correct fault handler has
   TINI *)

Theorem ni_concrete_machine : TINI tini_concrete_machine CMObservation.
Proof. unfold TINI. intros. eapply concrete_noninterference; eauto. Qed.

End Main.
