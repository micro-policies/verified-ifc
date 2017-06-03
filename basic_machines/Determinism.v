Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import Instr.
Require Import Concrete ConcreteMachine.

Set Implicit Arguments.
Local Open Scope Z_scope. 

(** The concrete machine is deterministic. *)

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

Lemma c_pop_to_return_determ : forall s s1,
  c_pop_to_return s s1 -> forall s2,
  c_pop_to_return s s2 -> s1 = s2.
Proof.
  induction 1; intros s2 H2; inv H2; auto; congruence.
Qed.

Lemma cmach_determ: 
  forall s e s' e' s'' 
    (STEP1: cstep s e s')
    (STEP2: cstep s e' s''),
    s' = s'' /\ e = e'.
  intros.
  destruct STEP1; inv STEP2;
  try (match goal with 
    | [H1 : cache_hit_read ?c ?rl _, 
       H2 : cache_hit_read ?c ?rl0 _ |- _ ] =>
  (exploit (@cache_hit_read_determ c rl); eauto; intros [Heq Heq'])
  end);
  try match goal with
        | [H1: c_pop_to_return ?s ?s1,
           H2: c_pop_to_return ?s ?s2 |- _ ] =>
          let EQ := fresh in
          assert (EQ:=@c_pop_to_return_determ _ _ POP _ POP0); inv EQ
      end;
  try match goal with
    | H1 : read_m _ _ = Some ?instr1,
      H2 : read_m _ _ = Some ?instr2 |- _ =>

      match constr:((instr1, instr2)) with
        | (?instr, ?instr) => idtac
        | _ =>
          let H := fresh in 
          assert (H : instr1 = instr2) by congruence; try discriminate;
          inversion H
      end
  end;
  try intuition congruence.
  Case "Call user".
    subst.
    exploit app_same_length_eq; eauto. intro Heq ; inv Heq.
    exploit app_same_length_eq_rest ; eauto. intro Heq ; inv Heq.
    split; reflexivity.

  Case "Call kernel".
    subst.
    exploit app_same_length_eq; eauto. intro Heq ; inv Heq.
    exploit app_same_length_eq_rest ; eauto. intro Heq ; inv Heq.
    split; reflexivity.

  Case "Ret user".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.
    try match goal with
        | [H1: c_pop_to_return ?s ?s1,
           H2: c_pop_to_return ?s ?s2 |- _ ] => 
        (exploit (@c_pop_to_return_spec3 _ _ _ _ _ _ _ _ _ H1); eauto; 
         exploit (@c_pop_to_return_spec3 _ _ _ _ _ _ _ _ _ H2); eauto; 
         exploit (@c_pop_to_return_spec2 _ _ _ _ _ _ _ _ _ H1); eauto; 
         exploit (@c_pop_to_return_spec2 _ _ _ _ _ _ _ _ _ H2); eauto)
        end; 
    intuition congruence.

  Case "Ret kernel".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.
    try match goal with
        | [H1: c_pop_to_return ?s ?s1,
           H2: c_pop_to_return ?s ?s2 |- _ ] => 
        (exploit (@c_pop_to_return_spec3 _ _ _ _ _ _ _ _ _ H1); eauto; 
         exploit (@c_pop_to_return_spec3 _ _ _ _ _ _ _ _ _ H2); eauto; 
         exploit (@c_pop_to_return_spec2 _ _ _ _ _ _ _ _ _ H1); eauto; 
         exploit (@c_pop_to_return_spec2 _ _ _ _ _ _ _ _ _ H2); eauto)
        end; 
    intuition congruence.
Qed.

End Determinism.
