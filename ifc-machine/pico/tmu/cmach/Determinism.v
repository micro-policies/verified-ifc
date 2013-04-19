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

Lemma cmach_priv_determ: 
  forall s s' s'', 
    cstep s s' -> 
    cstep s s'' -> 
    s' = s''.
Proof.
  induction 1; intros;
  match goal with 
      | [HH: cstep _ _ |- _ ] => inv HH; try congruence; auto
  end;
  try (match goal with 
    | [H1 : cache_hit_read ?c ?rl _, 
       H2 : cache_hit_read ?c ?rl0 _ |- _ ] =>
  (exploit (@cache_hit_read_determ c rl); eauto; intros [Heq Heq'])
  end);
  (allinv'; try reflexivity).
  
  Case "Call user".
    exploit app_same_length_eq; eauto. intro Heq ; inv Heq.
    exploit app_same_length_eq_rest ; eauto. intro Heq ; inv Heq.
    reflexivity.

  Case "Call kernel".
    exploit app_same_length_eq; eauto. intro Heq ; inv Heq.
    exploit app_same_length_eq_rest ; eauto. intro Heq ; inv Heq.
    reflexivity.

  Case "Ret user".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.
    
    exploit @c_pop_to_return_spec2; eauto.  move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros. 
    inv H. inv H0. 
    
    exploit @c_pop_to_return_spec3; eauto. clear POP.
    exploit @c_pop_to_return_spec3; eauto. 
    intros.  inv H.    
    reflexivity.

  Case "Ret kernel / user".
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
    reflexivity.
    
  Case "VRet".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto. intros. move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros. 

    exploit @c_pop_to_return_spec3; eauto. intros. 
    generalize POP0 ; clear POP0 ; intros POP0.
    exploit @c_pop_to_return_spec3; eauto. intros.
    inv H1.  inv H. inv H0.
    reflexivity.

  Case "VRet".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.

    exploit @c_pop_to_return_spec2; eauto. intros. move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros. 
    inv H. inv H0. 

  Case "Ret priv".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.
    
    exploit @c_pop_to_return_spec2; eauto.  move_to_top H11.
    exploit @c_pop_to_return_spec2; eauto. intros. 
    inv H1. inv H2. 
    
    exploit @c_pop_to_return_spec3; eauto. clear H0.
    exploit @c_pop_to_return_spec3; eauto. 
    intros.  inv H1.    
    reflexivity.

  Case "VRet cache hit and miss".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.
    
    exploit @c_pop_to_return_spec2; eauto.  move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros. 
    inv H. inv H0. 

  Case "Ret priv".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.
    
    exploit @c_pop_to_return_spec2; eauto.  move_to_top POP0.
    exploit @c_pop_to_return_spec2; eauto. intros. 
    inv H. inv H0. 
    
    exploit @c_pop_to_return_spec3; eauto. 

  Case "Ret priv true".
    exploit @c_pop_to_return_spec; eauto.
    intros [dstk [stk [a [b [p [Hs Hdstk]]]]]]. inv Hs.
    
    exploit @c_pop_to_return_spec2; eauto.  move_to_top H13.
    exploit @c_pop_to_return_spec2; eauto. intros. 
    inv H1. inv H2. 
    
    exploit @c_pop_to_return_spec3; eauto. clear H0.
    exploit @c_pop_to_return_spec3; eauto. 
    intros.  inv H1.    
    reflexivity.
Qed.

(* APT: This doesn't seem to be used.... 
Lemma cache_hit_same_content (T: Type): forall opcode labs pcl c c',
  cache_hit c opcode labs pcl ->
  cache_hit c' opcode labs pcl ->
  forall a, 
    (a = addrOpLabel \/ a = addrTag1 \/ a = addrTag2 \/ a = addrTag3 \/ a = addrTagPC) ->
    index_list_Z a c = index_list_Z a c'.
Proof.
  intros. inv H; inv H0. 
  destruct labs as [[l1 l2] l3]. 
  intuition; match goal with | [HH: a = _ |- _ ] => inv HH end.
  inv OP0. inv OP. congruence.
  inv TAG1 ; inv TAG0; congruence.
  inv TAG2 ; inv TAG4; congruence.
  inv TAG3 ; inv TAG5; congruence.
  inv TAGPC ; inv TAGPC0; congruence.
Qed.  
*)

End Determinism.