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

Lemma cmach_determ:
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
    | [H1 : cache_hit_read ?c ?rl _,
       H2 : cache_hit_read ?c ?rl0 _ |- _ ] =>
  (exploit (@cache_hit_read_determ c rl); eauto; intros [Heq Heq'])
  end);
  (allinv'; split ; try reflexivity).

  Case "Store user".
  allinv'. split ; reflexivity.

  Case "Call user".
    subst.
    exploit app_same_length_eq; eauto. intro Heq ; inv Heq.
    exploit app_same_length_eq_rest ; eauto. intro Heq ; inv Heq.
    split; reflexivity.

  Case "Call kernel".
    subst.
    exploit app_same_length_eq; eauto. intro Heq ; inv Heq.
    exploit app_same_length_eq_rest ; eauto. intro Heq ; inv Heq.
    split ; reflexivity.

  Case "Ret Ret user".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto.  move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros.
    inv H. inv H0.

    exploit @c_pop_to_return_spec3; eauto. clear POP.
    exploit @c_pop_to_return_spec3; eauto.
    intros.  inv H.
    split ; reflexivity.

  Case "Ret user".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto.  move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros.
    inv H. inv H0. congruence.

  Case "Ret kernel / user - sym".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto.  move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros.
    inv H. inv H0. congruence.

  Case "Ret kernel".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto.  move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros.
    inv H. inv H0.
    split ; reflexivity.

  Case "Ret Ret".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto.  move_to_top H12.
    exploit @c_pop_to_return_spec2; eauto. intros.
    inv H1. inv H2.

    exploit @c_pop_to_return_spec3; eauto. clear H0.
    exploit @c_pop_to_return_spec3; eauto.
    intros.  inv H1.
    split ; reflexivity.

  Case "VRet user ".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto. intros. move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros.

    exploit @c_pop_to_return_spec3; eauto. intros.
    generalize POP0 ; clear POP0 ; intros POP0.
    exploit @c_pop_to_return_spec3; eauto. intros.
    inv H1.  inv H. inv H0.
    split ; reflexivity.

  Case "Ret kernel / user ".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto.  move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros.
    inv H. inv H0.
    congruence.

  Case "Ret kernel / user - sym".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto.  move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros.
    inv H. inv H0.
    congruence.

  Case "VRet priv".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto.  move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros.
    inv H. inv H0.

    exploit @c_pop_to_return_spec3; eauto.

  Case "VRet true".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto. intros. move_to_top H14.
    exploit @c_pop_to_return_spec2; eauto. intros.
    inv H1. inv H2.

    exploit @c_pop_to_return_spec3; eauto. clear H0.
    exploit @c_pop_to_return_spec3; eauto. intros.
    inv H1.
    split ; reflexivity.
Qed.

End Determinism.
