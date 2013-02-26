Require Setoid.
Require RelationClasses.
Require Import Relations.
Require Import EqNat.
Require Import List.
Require Import Utils.

Set Implicit Arguments.

Section LNIwithEvents.

Variable E : Type.
Variable S : Type.
Variable O: Type.
Variable step: S -> S -> Prop.

Variable s_low : O -> S -> Prop.
Variable e_low : O -> E -> Prop.

Variable s_succ : S -> Prop.
Variable e_succ : E -> Prop.

Variable e : S -> E.
                            
CoInductive sys_trace : S -> trace E -> Prop :=
| oot_nil : forall s, 
             (forall s', ~ step s s') ->
             s_succ s ->
             sys_trace s (TCons (e s) TNil)
| oot_cons: forall s s' T,
             step s s' ->
             sys_trace s' (TCons (e s') T) ->
             sys_trace s (TCons (e s) (TCons (e s') T)).
Hint Constructors sys_trace.

Variable e_equiv : O -> relation E.

CoInductive lockstep_indist (O: O) : relation (trace E) :=
| li_lockstep_end : lockstep_indist O TNil TNil
| li_low_lockstep : forall s1 s2 t1 t2,
    e_low O s1 ->
    e_equiv O s1 s2 ->
    lockstep_indist O t1 t2 ->
    lockstep_indist O (TCons s1 t1) (TCons s2 t2)
| li_high_end1 : forall s1 s2 t2,
    ~(e_low O s1 /\ e_succ s1) ->
    e_equiv O s1 s2 ->
    lockstep_indist O (TCons s1 TNil) (TCons s2 t2)
| li_high_end2 : forall s1 s2 t1,
    ~(e_low O s2 /\ e_succ s2) ->
    e_equiv O s1 s2 ->
    lockstep_indist O (TCons s1 t1) (TCons s2 TNil)
| li_high_high1 : forall s1 s1' s2 t1 t2, 
    ~e_low O s1  ->
    ~e_low O s1' ->
    e_equiv O s1 s2 ->
    e_equiv O s1 s1' ->
    lockstep_indist O (TCons s1' t1) (TCons s2 t2) ->
    lockstep_indist O (TCons s1 (TCons s1' t1)) (TCons s2 t2)
| li_high_high2 : forall s1 s2 s2' t1 t2, 
    ~e_low O s2 ->
    ~e_low O s2' ->
    e_equiv O s1 s2 ->
    e_equiv O s2 s2' ->
    lockstep_indist O (TCons s1 t1) (TCons s2' t2) ->
    lockstep_indist O (TCons s1 t1) (TCons s2 (TCons s2' t2))
| li_high_low_lockstep : forall s1 s1' s2 s2' t1 t2,
    ~e_low O s1  ->
    ~e_low O s2  ->
    e_low O s1'  ->
    e_low O s2'  ->
    e_equiv O s1 s2 ->
    lockstep_indist O (TCons s1' t1) (TCons s2' t2) ->
    lockstep_indist O (TCons s1 (TCons s1' t1))
                    (TCons s2 (TCons s2' t2)).


Variable s_equiv : O -> relation S.

Context {Equiv : forall o, @RelationClasses.Equivalence S (s_equiv o)}.

Hint Extern 1 => 
  match goal with 
    | |- s_equiv _ _ _ => reflexivity
  end.

(* Hypothesis H_s_equiv_equiv : (forall o, equivalence _ (s_equiv o)). *)

Definition lockstep_ni : Prop := forall o s1 s2 t1 t2,
  s_equiv o s1 s2 ->
  sys_trace s1 t1 ->
  sys_trace s2 t2 ->
  lockstep_indist o t1 t2.

(** * Proof of lockstep non-interference *)
Hypothesis lowstep : forall o as1 as1' as2 as2',
  s_equiv o as1 as2 ->
  s_low o as1 ->
  step as1 as1' ->
  step as2 as2' ->
  s_equiv o as1' as2'.
       
Hypothesis highstep : forall o as1 as1', 
  ~s_low o as1 ->
  step as1 as1' ->
  ~s_low o as1' ->
  s_equiv o as1 as1'.

Hypothesis highlowstep : forall o as1 as1' as2 as2', 
  s_equiv o as1 as2 ->
  ~s_low o as1 ->
  step as1 as1' ->
  s_low o as1' ->
  step as2 as2' ->
  s_low o as2' ->
  s_equiv o as1' as2'.

Hypothesis low_lockstep_end : forall o s1 s1' s2,
  s_equiv o s1 s2 ->
  s_low o s2 ->
  step s1 s1' ->
  s_succ s2 ->
  False.

Hypothesis s_equiv_low: forall o s1 s2, s_equiv o s1 s2 -> (s_low o s1 <-> s_low o s2).

Hypothesis s_low_dec: forall o s, {s_low o s} + {~s_low o s}.
Hypothesis s_succ_dec: forall s, {s_succ s} + {~s_succ s}.

Hypothesis e_e_equiv : forall o s1 s2, s_equiv o s1 s2 -> e_equiv o (e s1) (e s2).

Hypothesis e_e_low : forall o s, s_low o s <-> e_low o (e s).
Hint Resolve e_e_low e_e_equiv : auto.

Ltac auto_low := 
  match goal with 
    | [H: s_low _ ?s |- e_low _ (_ ?s) ] => solve [apply e_e_low ; auto]
    | [n: ~ s_low _ ?s |- ~ (e_low _ (_ ?s) /\ _ ) ] => solve [rewrite e_e_low in n ; intuition]
    | [n: ~ s_low _ ?s |- ~ e_low _ (_ ?s) ] => solve [rewrite e_e_low in n ; intuition]
    | _ => auto
  end.
    
Theorem lockstep_ni_holds : lockstep_ni.
Proof.
  unfold lockstep_ni. cofix. intros. 
  inv H0; inv H1. 
  
  Case "s1 and s2 irred".
     destruct (s_low_dec o s1).
     SCase "low_pc s1".
     apply li_low_lockstep; auto_low.
     apply li_lockstep_end.     
     SCase "~low_pc s1".
     apply li_high_end1; auto_low.
  Case "s1 irred, not s2".
    destruct (s_low_dec o s1).
    SCase "low_pc s1".
    apply False_ind.
      apply low_lockstep_end with o s2 s' s1; eauto.
      symmetry ; auto.
    SCase "~low_pc s1".
      apply li_high_end1; auto_low.
  Case "s2 irred, not s1".
    destruct (s_low_dec o s2).
    SCase "low_pc s2".
      destruct (s_succ_dec s2).
      SSCase "success s2".  apply False_ind;  eauto using low_lockstep_end.
      SSCase "~success s2". apply li_high_end2; tauto.
   SCase "~low_pc s2". apply li_high_end2; auto_low.

  Case "both s1 and s2 reduce".
    destruct (s_low_dec o s1).
    SCase "low_pc s1".
      apply li_low_lockstep; auto_low. 
      apply lockstep_ni_holds with s' s'0 ; eauto. 
    SCase "~low_pc s1".
      destruct (s_low_dec o s').
      SSCase "low_pc s'".
        destruct (s_low_dec o s'0).
        SSSCase "low_pc s'0".
          assert (~ s_low o s2) by (eelim s_equiv_low; eauto).
          apply li_high_low_lockstep; auto_low. 
          eapply lockstep_ni_holds with s' s'0; eauto.
        SSSCase "~low_pc s'0".
          assert(~ s_low o s2) by
            (eelim s_equiv_low; eauto ; assumption).
          assert(s_equiv o s2 s'0) by eauto using highstep.
          apply li_high_high2; auto_low. 
          eapply lockstep_ni_holds with s1 s'0 ; eauto. 
          etransitivity; eauto.
      SSCase "~low_pc s1' (similar to previous SSSCase)".
        assert(s_equiv o s1 s') by eauto using highstep.
        apply li_high_high1; auto_low.
          eapply lockstep_ni_holds with s' s2 ; eauto. 
          symmetry in H1.
          etransitivity; eauto.
Qed.

End LNIwithEvents.

Section LNIwithStateEvents.

Variable S: Type.
Variable O: Type.
Variable step: S -> S -> Prop.
Variable s_low: O -> S -> Prop.
Variable s_succ: S -> Prop.
Variable s_equiv : O -> S -> S -> Prop.

Context {Equiv : forall o, @RelationClasses.Equivalence S (s_equiv o)}.

Hypothesis s_equiv_low: forall o s1 s2, s_equiv o s1 s2 -> (s_low o s1 <-> s_low o s2).
Hypothesis s_low_dec: forall o s, {s_low o s} + {~s_low o s}.
Hypothesis s_succ_dec: forall s, {s_succ s} + {~s_succ s}.

Hypothesis lowstep : forall o as1 as1' as2 as2',
  s_equiv o as1 as2 ->
  s_low o as1 ->
  step as1 as1' ->
  step as2 as2' ->
  s_equiv o as1' as2'.
       
Hypothesis highstep : forall o as1 as1', 
  ~s_low o as1 ->
  step as1 as1' ->
  ~s_low o as1' ->
  s_equiv o as1 as1'.

Hypothesis highlowstep : forall o as1 as1' as2 as2', 
  s_equiv o as1 as2 ->
  ~s_low o as1 ->
  step as1 as1' ->
  s_low o as1' ->
  step as2 as2' ->
  s_low o as2' ->
  s_equiv o as1' as2'.

Hypothesis low_lockstep_end : forall o s1 s1' s2,
  s_equiv o s1 s2 ->
  s_low o s2 ->
  step s1 s1' ->
  s_succ s2 ->
  False.

Definition lockstep_ni_state_evt := 
  lockstep_ni step s_low s_succ s_succ (fun x => x) s_equiv s_equiv.
  
Theorem lockstep_ni_state_evt_holds : lockstep_ni_state_evt.
Proof.
  unfold lockstep_ni_state_evt.
  eapply lockstep_ni_holds with (e_low := s_low); eauto.
  intuition. 
Qed.

End LNIwithStateEvents.