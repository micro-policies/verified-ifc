Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import Lattices.
Require Import AbstractObsEquiv.
Require Import TMUInstr.
Require Import Abstract.
Require Import Rules.
Require Import AbstractCommon.
Require Import AbstractMachine.
Require Import LNIwithEvents.
Require TINI.
Require Import LowStep.
Require Import HighStep.
Require Import HighLowStep.

Set Implicit Arguments.

(** * Non-interference property *)

(** Instantiating the generic lockstep non-interference property for
    our particular abstract machine *)

Section ParamMachine.

Context {T: Type}.
Context {Latt: JoinSemiLattice T}.

Ltac exploit_low :=
    repeat match goal with 
        | [H: low_equiv_list _ (_::_) (_::_) |- _ ] => inv H
        | [H: low_equiv_stkelt _ (AData _) (AData _) |- _ ] => inv H
        | [H: low_equiv_stkelt _ (ARet _ _) (ARet _ _) |- _ ] => inv H
    end.

Ltac spec_pop_return :=
  (exploit @pop_to_return_spec; eauto);
  let stk := fresh "stk" in
  let Hstk := fresh "Hstk" in
  (intros [? [? [? [? [Hstk ?]]]]]);
  match type of Hstk with 
    | ?aastk = _ =>
      match goal with 
        | [HH: pop_to_return aastk _ |- _ ] => (subst ; move_to_top HH)
      end
  end.

Lemma low_lockstep_end : forall o s1 e s1' s2,
  low_equiv_full_state o s1 s2 ->
  low_pc o s2 ->
  step_rules s1 e s1' ->
  success s2 ->
  False.
Proof.
  intros. 
  apply low_equiv_low_success in H; trivial.
  eapply success_runSTO_None in H; eauto.
Qed.

Program Instance AMUnwindingSemantics : TINI.UnwindingSemantics := {
  state := AS;
  event := option Event;
  step := step_rules;

  observer := T;

  s_equiv := low_equiv_full_state;
  s_low := low_pc;
  s_low_dec := low_pc_dec;

  e_equiv := low_equiv_event;
  e_low := visible_event;
  e_low_dec := visible_event_dec
}.

Next Obligation.
  intros x y H. rewrite <- H. reflexivity.
Qed.

Next Obligation.
  inv H; split; intros H; inv H; try congruence;
  unfold low_pc; simpl; trivial.
Qed.

Next Obligation.
  inv H; split; intros H; inv H; auto;
  match goal with
    | H : ~ visible_event o (Some (EInt (?i, ?l))) |- _ =>
      contradict H
  end;
  constructor;
  trivial.
Qed.

Next Obligation.
  unfold low_pc.
  inv H; simpl;
  try match goal with
        | H : visible_event _ _ |- _ =>
          inv H
      end.
  eauto with lat.
Qed.

Next Obligation.
  repeat match goal with
           | e1 : option Event,
             e2 : option Event |- _ =>
             destruct e1; destruct e2
         end;
  try solve [constructor (solve [eauto])].
Qed.

Next Obligation.
  inv H1; inv H2;
  try solve [econstructor (intros H'; inv H'; solve [eauto])];
  match goal with
    | H : low_equiv_full_state _ _ _ |- _ =>
      inv H
  end;
  try solve [
        constructor; intros H; inv H;
        match goal with
          | H1 : ?pcl <: ?o = false,
            H2 : ?l \_/ ?pcl <: ?o = true |- _ =>
            apply join_2_rev in H2; congruence
        end
      ];
  try solve [exploit @index_list_Z_low_eq_instr; eauto; intros H; inv H].
  inv LEs.
  inv H5.
  inv LEa; try reflexivity.
  constructor; intros H; inv H;
  match goal with
    | H : ?l \_/ ?pcl <: ?o = true |- _ =>
      apply join_1_rev in H; congruence
  end.
Qed.

Next Obligation.
  eapply lowstep; eauto.
Qed.

Next Obligation.
  rewrite <- H0.
  symmetry.
  eapply highstep; eauto.
Qed.

Next Obligation.
  eapply highlowstep; eauto.
Qed.

Theorem noninterference : TINI.tini.
Proof. apply TINI.noninterference. Qed.

(* Theorem lockstep_ni_amach : *)
(*   lockstep_ni_state_evt step_rules low_pc success low_equiv_full_state. *)
(* Proof.  *)
(*   eapply lockstep_ni_state_evt_holds ; eauto. *)

(*   intros; split ; eauto using pc_labels1, pc_labels2.  *)
(*   exact low_pc_dec.  *)
(*   exact success_dec. *)
  
(*   eapply lowstep; eauto. *)
(*   eapply highstep; eauto. *)
(*   eapply highlowstep; eauto. *)
(*   eapply low_lockstep_end; eauto.   *)
(* Qed. *)

End ParamMachine.
