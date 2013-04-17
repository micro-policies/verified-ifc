Require Import Relations.
Require Import EqNat.
Require Import List.
Require Import Utils.
Require Import Monad.
Require Import NotionsOfNI.

Set Implicit Arguments.

Section LockStepNI.

(* States and transition relation on states *)
Variable S: Type.
Definition SMach := STO S.
Variable step: SMach unit.
 
(* Traces starting from the state s *) 
CoFixpoint trace_of (s : S) : trace S :=
  TCons s (match runSTO step s with
           | None => TNil
           | Some s' => trace_of s'
           end).

Lemma trace_of_cons : forall s,
  trace_of s = TCons s (match runSTO step s with
                       | None => TNil
                       | Some s' => trace_of s'
                       end).
Proof. 
  intros. 
  rewrite frob_eq at 1. reflexivity. 
Qed.

Inductive sys_trace_smach : trace S -> Prop :=
  | sta : forall s, sys_trace_smach (trace_of s).

Lemma sys_trace_smach_cons: forall t s, 
                              t <> TNil ->
                              sys_trace_smach (TCons s t) ->
                              sys_trace_smach t.
Proof.
  intros.
  destruct t ; intuition.
  inv H0.
  rewrite trace_of_cons in H2.
  inv H2.
  destruct runSTO. 
  constructor. 
  inv H3.
Qed.
  
Variable Observer: Type.

Variable equiv : Observer -> relation S.
Hypothesis H_equiv : forall o, equivalence _ (equiv o).

Variable Low : Observer -> S -> Prop.
Hypothesis Low_dec: forall o s, {Low o s} + {~Low o s}.

Hypothesis pc_labels: forall o s1 s2,
  equiv o s1 s2 ->
  (Low o s1 <-> Low o s2).

Variable Succ : S -> Prop.
Hypothesis Succ_dec: forall s, {Succ s} + {~Succ s}.

Definition lockstep_ni_smach :=
  lockstep_ni sys_trace_smach equiv Low  Succ.

(** * Proof of lockstep non-interference *)
Hypothesis lowstep : forall o as1 as1' as2 as2', 
  equiv o as1 as2 ->
  Low o as1 ->
  runSTO step as1 = Some as1' ->
  runSTO step as2 = Some as2' ->
  equiv o as1' as2'.
       
Hypothesis highstep : forall o as1 as1', 
  ~Low o as1 ->
  runSTO step as1 = Some as1' ->
  ~Low o as1' ->
  equiv o as1 as1'.

Hypothesis highlowstep : forall o as1 as1' as2 as2', 
  equiv o as1 as2 ->
  ~Low o as1 ->
  runSTO step as1 = Some as1' ->
  Low o as1' ->
  runSTO step as2 = Some as2' ->
  Low o as2' ->
  equiv o as1' as2'.

Hypothesis low_lockstep_end : forall o s1 s1' s2,
  equiv o s1 s2 ->
  Low o s2 ->
  runSTO step s1 = Some s1' ->
  runSTO step s2 = None ->
  Succ s2 ->
  False.

Theorem lockstep_ni_smach_holds : lockstep_ni_smach.
Proof.
  (* start with some simplifications *)
  unfold lockstep_ni_smach, lockstep_ni. intros.
  inv H0. inv H1. rewrite trace_of_cons in H2. inv H2.
                  rewrite trace_of_cons in H3. inv H3.
  (* proof by coinduction *)
  gdep s2. gdep s1. cofix. intros.
  do 2 rewrite trace_of_cons.
  remember (runSTO step s1) as o1;
    destruct o1 as [s1' |]; symmetry in Heqo1;
  remember (runSTO step s2) as o2;
    destruct o2 as [s2' |]; symmetry in Heqo2.
  Case "both s1 and s2 reduce".
    destruct (Low_dec o s1).
    SCase "low_pc s1".
      apply li_low_lockstep; try assumption.
      apply lockstep_ni_smach_holds.
      solve [eauto using lowstep].
    SCase "~low_pc s1".
      destruct (Low_dec o s1').
      SSCase "low_pc s1'".
        destruct (Low_dec o s2').
        SSSCase "low_pc s2'".
          do 2 rewrite trace_of_cons. apply li_high_low_lockstep; trivial.
          eelim pc_labels;
            eauto using (@equiv_trans _ (equiv o)).
          do 2 rewrite <- trace_of_cons. apply lockstep_ni_smach_holds.
          eauto using highlowstep.
        SSSCase "~low_pc s2'".
          assert(~Low o s2) by
            (eelim pc_labels; eauto ;assumption).
          assert(equiv o s2 s2') by eauto using highstep.
          rewrite trace_of_cons with (s:=s2'). apply li_high_high2; trivial.
          rewrite <- trace_of_cons.
          replace (TCons s1 (trace_of s1')) with (trace_of s1)
            by (rewrite trace_of_cons; rewrite Heqo1; reflexivity).
          apply lockstep_ni_smach_holds.
          eapply (@equiv_trans _ (equiv o)); eauto. 
      SSCase "~low_pc s1' (similar to previous SSSCase)".
        assert(equiv o s1 s1') by eauto using highstep.
        rewrite trace_of_cons. apply li_high_high1; trivial.
        rewrite <- trace_of_cons.
        replace (TCons s2 (trace_of s2')) with (trace_of s2)
          by (rewrite trace_of_cons; rewrite Heqo2; reflexivity).
        apply lockstep_ni_smach_holds.
        eapply (@equiv_trans _ (equiv o)) with s1; eauto.
        eapply (@equiv_sym _ (equiv o)) ; eauto.        
  Case "s2 irred".
    destruct (Low_dec o s2).
    SCase "low_pc s2".
      destruct (Succ_dec s2).
      SSCase "success s2". apply False_ind; eauto using low_lockstep_end.
      SSCase "~success s2". apply li_high_end2; tauto.
    SCase "~low_pc s2". apply li_high_end2; tauto.
  Case "s1 irred (symmetric to the previous case)".
    destruct (Low_dec o s1).
    SCase "low_pc s1".
      destruct (Succ_dec s1).
      SSCase "success s1". apply False_ind. 
      apply low_lockstep_end with o s2 s2' s1; eauto.
      eapply (@equiv_sym _ (equiv o)); eauto.
      SSCase "~success s1". apply li_high_end1; tauto.
    SCase "~low_pc s1". apply li_high_end1; tauto.
  Case "s1 and s2 irred".
    destruct (Low_dec o s1).
    SCase "low_pc s1". eauto using li_low_lockstep, li_lockstep_end.
    SCase "~low_pc s1". apply li_high_end1; tauto.
Qed.

End LockStepNI.