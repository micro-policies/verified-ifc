(* These auxiliary definitions and lemmas are used in the semantics of
the abstract and quasi-abstract machines. *)

Require Import List.

Require Import Utils.
Require Import Lattices.

Require Import TMUInstr.
Require Import Abstract.

Set Implicit Arguments.

Local Open Scope Z_scope.

Section ARuleMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

Inductive pop_to_return : list (@StkElmt T) -> list (@StkElmt T) -> Prop :=
| sptr_done: forall a b s,
    pop_to_return ((ARet a b)::s) ((ARet a b)::s)
| sptr_pop: forall a s s',
    pop_to_return s s' ->
    pop_to_return ((AData a)::s) s'.

Lemma pop_to_return_ret : forall s1 s2,
  pop_to_return s1 s2 ->
  exists a b s, s2 = (@ARet T a b)::s.
Proof.
  induction 1; intros; simpl; eauto.
Qed.

Lemma pop_to_return_spec : forall s1 s2,
  pop_to_return s1 s2 ->
  exists dstk, exists stk a b,
    s1 = dstk++(ARet a b)::stk
    /\ (forall e, In e dstk -> exists a, e = AData a).
Proof.
  induction 1; intros; simpl in *.
  exists nil ; exists s ; exists a ; exists b.
  simpl ; split ; eauto.
  intuition.

  destruct IHpop_to_return as [dstk [stk [a0 [b0 [Hs Hdstk]]]]].
  subst.
  exists ((AData a)::dstk).
  exists stk ; eauto.
  exists a0 ; exists b0 ; split ; eauto.
  intros. inv H0.
  eauto.
  eapply Hdstk; auto.
 Qed.

Lemma pop_to_return_spec2: forall  s1 s2  b1 b2 a1 a2 dstk,
 pop_to_return (dstk ++ ARet a1 b1 :: s2)
               (ARet a2 b2 :: s1) ->
 (forall e : StkElmt, In e dstk -> exists a : @Atom T, e = AData a) ->
 ARet a1 b1 =  ARet a2 b2.
Proof.
  induction dstk; intros.
  inv H. auto.
  simpl in *.
  inv H. destruct (H0 (ARet a2 b2)). intuition. inv H.
  eapply IHdstk; eauto.
Qed.

Lemma pop_to_return_spec3: forall s1 s2 b1 b2 a1 a2 dstk,
 pop_to_return (dstk ++ ARet a1 b1 :: s2)
               (ARet a2 b2 :: s1) ->
 (forall e, In e dstk -> exists a : @Atom T, e = AData a) ->
 s1 = s2 .
Proof.
  induction dstk; intros.
  inv H. auto.
  simpl in *.
  inv H. destruct (H0 (ARet a2 b2)). intuition. inv H.
  eapply IHdstk; eauto.
Qed.

Lemma spec_find_return :
  forall (T : Type)  (stk : list (@StkElmt T)) a b s,
    find_return stk = Some (a, b, s) ->
    (exists stk' : list StkElmt,
       (forall e, In e stk' -> exists a, e = AData a) /\
       stk = stk' ++ ((ARet a b):: s)).
Proof.
  induction stk; intros.
  inv H.
  simpl in *. destruct a.
  exploit IHstk; eauto. intros [stk' [Hdata Hstk]].
  rewrite Hstk. exists (AData a :: stk'). split ; auto.
  intros. inv H0 ; auto. eauto.
  inv H.
  exists nil. split ; auto.
  intros. inv H.
Qed.

End ARuleMachine.
