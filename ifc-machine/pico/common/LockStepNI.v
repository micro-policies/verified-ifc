Require Import Relations.
Require Import EqNat.
Require Import List.
Require Import Utils.
Require Import NotionsOfNI.

Set Implicit Arguments.

Section LockStepNI.

(* States and transition relation on states *)
Variable S: Type.
Variable step: S -> S -> Prop.

CoInductive sys_trace_smach : trace S -> Prop :=
| sta_nil : forall s T,
    (forall s', ~ step s s') -> 
    T = (TCons s TNil) ->
    sys_trace_smach T
| sta_cons: forall s s' T T',
    step s s' ->
    sys_trace_smach (TCons s' T) ->
    T' = (TCons s (TCons s' T)) ->
    sys_trace_smach T'.

Lemma sys_trace_smach_cons: forall t s, 
                              t <> TNil ->
                              sys_trace_smach (TCons s t) ->
                              sys_trace_smach t.
Proof.
  intros.
  destruct t ; intuition.
  inv H0. inv H2. inv H3.  auto.
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
  step as1 as1' ->
  step as2 as2' ->
  equiv o as1' as2'.
       
Hypothesis highstep : forall o as1 as1', 
  ~Low o as1 ->
  step as1 as1' ->
  ~Low o as1' ->
  equiv o as1 as1'.

Hypothesis highlowstep : forall o as1 as1' as2 as2', 
  equiv o as1 as2 ->
  ~Low o as1 ->
  step as1 as1' ->
  Low o as1' ->
  step as2 as2' ->
  Low o as2' ->
  equiv o as1' as2'.

Hypothesis low_lockstep_end : forall o s1 s1' s2,
  equiv o s1 s2 ->
  Low o s2 ->
  step s1 s1' ->
  Succ s2 ->
  False.

Lemma trace_step: forall s t,
  sys_trace_smach (TCons s t) ->
                         t = TNil \/ 
                         exists s', exists t', step s s' /\ sys_trace_smach t'.
Proof.
  intros.
  inv H. inv H1. auto. 
  right.  inv H2. eauto.
Qed.

Theorem lockstep_ni_smach_holds : lockstep_ni_smach.
Proof.
  (* start with some simplifications *)
  unfold lockstep_ni_smach, lockstep_ni. intros.
  (* proof by coinduction *)
  gdep s2. gdep s1. gdep t2. gdep t1. cofix. intros. 
  inv H0. inv H1. 
  
  Case "s1 and s2 irred".
     destruct (Low_dec o s1).
     SCase "low_pc s1". 
     inversion H3. inversion H4. 
     apply li_low_lockstep; auto. 
     rewrite <- H5. auto.
     rewrite <- H7. rewrite <- H5. auto.
     eapply li_lockstep_end; eauto.
     SCase "~low_pc s1". 
     inversion H3. inversion H4. 
     rewrite <- H5. rewrite <- H7. 
     apply li_high_end1; tauto.

  Case "s1 irred, not s2".
    destruct (Low_dec o s1).
    SCase "low_pc s1".
      destruct (Succ_dec s1).
      SSCase "success s1". apply False_ind. 
      apply low_lockstep_end with o s2 s' s1; eauto.
      eapply (@equiv_sym _ (equiv o)); eauto.
      inversion H5. auto. 
      SSCase "~success s1". 
      inversion H3.
      inversion H5. rewrite <- H5.      
      rewrite H8 in *.
      rewrite H6 in *.
      apply li_high_end1; tauto. 
    SCase "~low_pc s1". 
      inversion H3. inversion H5. 
      rewrite <- H5. rewrite H8 in *.
      rewrite H6 in *.    
      apply li_high_end1; tauto.

  inv H1.
  Case "s2 irred, not s1".
    destruct (Low_dec o s2).
    SCase "low_pc s2".
      destruct (Succ_dec s2).
      SSCase "success s2". 
      inversion H4. inversion H5.
      rewrite <- H7 in *. rewrite <- H8 in *. rewrite <- H6 in *.
      apply False_ind;  eauto using low_lockstep_end. 
      SSCase "~success s2". 
      inversion H4.  inversion H5.
      rewrite <- H6 in *. rewrite <- H7 in *.  rewrite <- H8 in *.
      apply li_high_end2; tauto. 
   SCase "~low_pc s2". 
      inversion H4. inversion H5. 
      rewrite <- H8 in *. rewrite <- H6 in *.    
      apply li_high_end2; tauto.

  Case "both s1 and s2 reduce".
    destruct (Low_dec o s1).
    SCase "low_pc s1".
      apply li_low_lockstep; try assumption. 
      inversion H4. inversion H6.
      apply lockstep_ni_smach_holds; auto. 
      rewrite <- H7 in *. rewrite <- H9 in *.
      solve [eauto using lowstep]. 
    SCase "~low_pc s1".
      destruct (Low_dec o s').
      SSCase "low_pc s1'".
        destruct (Low_dec o s'0).
        SSSCase "low_pc s2'".
          inversion H4. inversion H6. rewrite <- H9 in *. rewrite <- H7 in *.
          apply li_high_low_lockstep; trivial.
          eelim pc_labels;
            eauto using (@equiv_trans _ (equiv o)).
          apply lockstep_ni_smach_holds; try assumption.
          eauto using highlowstep.          
        SSSCase "~low_pc s2'".
          inversion H4. inversion H6.
          rewrite <- H9 in *. rewrite <- H7 in *.
          assert(~Low o s2) by
            (eelim pc_labels; eauto ; assumption).
          assert(equiv o s2 s'0) by eauto using highstep.
          apply li_high_high2; trivial. 
          apply lockstep_ni_smach_holds. apply sta_cons with s1 s' T; auto.
          eapply (@equiv_trans _ (equiv o)); eauto. auto.  
      SSCase "~low_pc s1' (similar to previous SSSCase)".
        inversion H4. inversion H6.
        rewrite <- H9 in *. rewrite <- H7 in *.
        assert(equiv o s1 s') by eauto using highstep.
        apply li_high_high1; trivial.
        apply lockstep_ni_smach_holds; auto.
        eapply (@equiv_trans _ (equiv o)) with s1; eauto.
        eapply (@equiv_sym _ (equiv o)) ; eauto.        
        eapply sta_cons; eauto.
Qed.

End LockStepNI.