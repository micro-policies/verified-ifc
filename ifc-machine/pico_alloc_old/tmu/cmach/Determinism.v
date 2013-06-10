(* The concrete machine is deterministic. *)

Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import Utils.

Require Import TMUInstr.
Require Import Abstract Rules AbstractMachine.

Require Import Concrete ConcreteMachineSmallStep.

Set Implicit Arguments.
Local Open Scope Z_scope. 
(* Coercion Z_of_nat : nat >-> Z. *)

Section Determinism.

Ltac allinv' :=
  allinv ; 
    (match goal with 
       | [ H1:  ?f _ _ = _ , 
           H2:  ?f _ _ = _ |- _ ] => rewrite H1 in H2 ; inv H2
     end).

Lemma cache_hit_read_determ: forall c rl1 rpcl1 rl2 rpcl2,
  cache_hit_read c rl1 rpcl1 -> 
  cache_hit_read c rl2 rpcl2 ->
  rl1 = rl2 /\ rpcl1 = rpcl2. 
Proof.
  intros. inv H. inv TAG_Res. inv TAG_ResPC. 
  inv H0. inv TAG_Res. inv TAG_ResPC. 
  allinv'. allinv'. intuition.
Qed.

Lemma cache_hit_read_mem_determ: forall m rl1 rpcl1 rl2 rpcl2,
  cache_hit_read_mem m rl1 rpcl1 -> 
  cache_hit_read_mem m rl2 rpcl2 ->
  rl1 = rl2 /\ rpcl1 = rpcl2. 
Proof.
  unfold cache_hit_read_mem; intros.
  destruct Mem.get_frame.
  + eapply cache_hit_read_determ; eauto.
  + intuition.  
Qed.

Lemma c_pop_to_return_determ : forall s s1,
  c_pop_to_return s s1 -> forall s2,
  c_pop_to_return s s2 -> s1 = s2.
Proof.
  induction 1; intros s2 H2; inv H2; auto; congruence.
Qed.

Lemma cmach_priv_determ_state: 
  forall s e s' e' s'', 
    cstep s e s' -> 
    cstep s e' s'' -> 
    s' = s'' /\ e = e'.
Proof.
  induction 1; intros;
  match goal with 
      | [HH: cstep _ _ _ |- _ ] => inv HH; try congruence; auto
  end;
  try (match goal with 
    | [H1 : cache_hit_read_mem ?m ?rl _, 
       H2 : cache_hit_read_mem ?m ?rl0 _ |- _ ] =>
  (exploit (@cache_hit_read_mem_determ m rl); eauto; intros [Heq Heq'])
  end);
  try match goal with
        | [H1: c_pop_to_return ?s ?s1,
           H2: c_pop_to_return ?s ?s2 |- _ ] =>
          let EQ := fresh in
          assert (EQ:=@c_pop_to_return_determ _ _ POP _ POP0); inv EQ
      end;          
  try match goal with
        | [H1: ~ ?P, H2: ?P |- _] => elim H1; exact H2
      end;
  (allinv'; split ; try reflexivity).

  Case "Store user".
  allinv'. split ; reflexivity.
  
  Case "Call user".
    exploit app_same_length_eq; eauto. intro Heq ; inv Heq.
    exploit app_same_length_eq_rest ; eauto. intro Heq ; inv Heq.
    split ; reflexivity.

  Case "Call kernel".
    exploit app_same_length_eq; eauto. intro Heq ; inv Heq.
    exploit app_same_length_eq_rest ; eauto. intro Heq ; inv Heq.
    split ; reflexivity.
Qed.


End Determinism.