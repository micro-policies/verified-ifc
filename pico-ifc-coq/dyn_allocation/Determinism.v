(* The concrete machine is deterministic. *)

Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import Utils.

Require Import Instr Memory.

Require Import Concrete ConcreteMachine ConcreteExecutions.

Set Implicit Arguments.
Local Open Scope Z_scope. 

Section Determinism.


Lemma cache_hit_read_determ: forall c rl1 rpcl1 rl2 rpcl2,
  cache_hit_read c rl1 rpcl1 -> 
  cache_hit_read c rl2 rpcl2 ->
  rl1 = rl2 /\ rpcl1 = rpcl2. 
Proof.
  intros. inv H. inv TAG_Res. inv TAG_ResPC. 
  inv H0. inv TAG_Res. inv TAG_ResPC. 
  allinv'. allinv'. intuition.
Qed.

Lemma cache_hit_read_mem_determ: forall cblock m rl1 rpcl1 rl2 rpcl2,
  cache_hit_read_mem cblock m rl1 rpcl1 -> 
  cache_hit_read_mem cblock m rl2 rpcl2 ->
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

Lemma cmach_determ:
  forall cblock s e s' e' s''
         (STEP1: cstep cblock s e s')
         (STEP2: cstep cblock s e' s''),
    s' = s'' /\ e = e'.
Proof.
  intros.
  destruct STEP1;
  rewrite CS1 in *; rewrite CA in *; rewrite CS2 in *;
  clear CS1 CA CS2; destruct STEP2; try discriminate;
  match goal with
    | H1 : read_m _ _ = Some ?instr1,
      H2 : read_m _ _ = Some ?instr2 |- _ =>
      match constr:(instr1, instr2) with
        | (?instr, ?instr) => idtac
        | _ =>
          assert (H : instr1 = instr2) by congruence; try discriminate;
          inversion H
      end
  end;
  inv CS1;
  try (match goal with
    | [H1 : cache_hit_read_mem ?cb ?m ?rl _,
       H2 : cache_hit_read_mem ?cb ?m ?rl0 _ |- _ ] =>
  (exploit (@cache_hit_read_mem_determ cb m rl); eauto; intros [Heq Heq'])
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
  subst; split; try congruence.

  Case "Call user".
    exploit app_same_length_eq; eauto. intro Heq ; inv Heq.
    exploit app_same_length_eq_rest ; eauto. intro Heq ; inv Heq.
    split ; reflexivity.

  Case "Call kernel".
    exploit app_same_length_eq; eauto. intro Heq ; inv Heq.
    exploit app_same_length_eq_rest ; eauto. intro Heq ; inv Heq.
    split ; reflexivity.
Qed.

Lemma runsUntilUser_determ :
  forall cblock s1 s21 s22
         (RUN1 : runsUntilUser cblock s1 s21)
         (RUN2 : runsUntilUser cblock s1 s22),
    s21 = s22.
Proof.
  intros.
  induction RUN1; inv RUN2;
  try match goal with
        | [ H1 : cstep _ ?s _ _,
            H2 : cstep _ ?s _ _
            |- _ ] =>
          let H := fresh "H" in
          generalize (cmach_determ H1 H2);
          intros [? ?]; subst
      end; eauto;
  try match goal with
        | [ H : runsUntilUser _ _ _ |- _ ] =>
          generalize (runsUntilUser_l H);
          intros
      end;
  congruence.
Qed.

End Determinism.
