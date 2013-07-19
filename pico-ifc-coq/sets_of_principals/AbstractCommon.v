(* These auxiliary definitions and lemmas are used in the semantics of
the abstract and quasi-abstract machines. *)

Require Import List.
Require Import Utils.

Require Import Lattices.
Require Import Instr.

Set Implicit Arguments.

Local Open Scope Z_scope.

Inductive StkElmt {T:Type} := 
| AData : @Atom T -> @StkElmt T
| ARet : @Atom T -> bool -> @StkElmt T.
(* CH: not sure which variant is better, but in the Haskell version
       the bool in ARet is labeled by the same label as the int *)

Record AS {T: Type}  := AState {
  amem : list (@Atom T);
  aimem : list Instr;
  astk : list (@StkElmt T);
  apc : @Atom T  
}.

Inductive Event {T: Type} :=
| EInt : @Atom T -> @Event T.

Hint Resolve @flows_refl @flows_join_right  @flows_join_left.

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

End ARuleMachine.
