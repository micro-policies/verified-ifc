(* These auxiliary definitions and lemmas are used in the semantics of
the abstract and quasi-abstract machines. *)

Require Import List.
Require Import Utils.

Require Import Lattices.
Require Import Instr Memory.

Set Implicit Arguments.

Local Open Scope Z_scope.

Inductive StkElmt {T S} := 
| AData : Atom T S -> StkElmt
| ARet : PcAtom T -> bool -> StkElmt.
Implicit Arguments StkElmt [].
(* CH: not sure which variant is better, but in the Haskell version
       the bool in ARet is labeled by the same label as the int *)

Record AS {T S}  := AState {
  amem : memory T S;
  aimem : list Instr;
  astk : list (StkElmt T S);
  apc : PcAtom T  
}.
Implicit Arguments AS [].

(* DD -> DP: is PcAtom supposed to restrict the kind of output values?
             at some point, I guess the code is going to be put in memory too, at
             which point PcAtom will be also a pointer. Change it to ZAtom?
*)
Inductive Event {T: Type} :=
| EInt : PcAtom T -> @Event T.
Implicit Arguments Event [].

Hint Resolve @flows_refl @flows_join_right  @flows_join_left.

(* Same for both the abstract and quasi-abstract machines *)
Definition abstract_init_data T :=
  (list Instr * list (PcAtom T) * T)%type.

Section ARuleMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {S: Type}.

Inductive pop_to_return : list (StkElmt T S) -> list (StkElmt T S) -> Prop :=
| sptr_done: forall a b s,
    pop_to_return ((ARet a b)::s) ((ARet a b)::s)
| sptr_pop: forall a s s',
    pop_to_return s s' ->
    pop_to_return ((AData a)::s) s'.

Lemma pop_to_return_ret : forall s1 s2,
  pop_to_return s1 s2 ->
  exists a b s, s2 = (ARet a b)::s.
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

Lemma pop_to_return_spec2: forall  s1 s2 b1 b2 a1 a2 dstk,
 pop_to_return (dstk ++ ARet a1 b1 :: s2)
               (ARet a2 b2 :: s1) ->
 (forall e : StkElmt T S, In e dstk -> exists a : Atom T S, e = AData a) ->
 @ARet T S a1 b1 =  @ARet T S a2 b2.
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
 (forall e, In e dstk -> exists a : Atom T S, e = AData a) ->
 s1 = s2 .
Proof.
  induction dstk; intros.
  inv H. auto.
  simpl in *.
  inv H. destruct (H0 (ARet a2 b2)). intuition. inv H.
  eapply IHdstk; eauto.
Qed.

End ARuleMachine.

Record ASysCall T S : Type := {
  asi_arity : nat;
  asi_sem : list (Atom T S) -> option (Atom T S)
}.

Definition ASysTable T S : Type := ident -> option (ASysCall T S).
