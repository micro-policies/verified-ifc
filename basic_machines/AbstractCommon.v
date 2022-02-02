Require Import List.
Require Import Utils.

Require Import Lattices.
Require Import Instr.

Set Implicit Arguments.

Local Open Scope Z_scope.

(** These auxiliary definitions and lemmas are used in the semantics of
the abstract and quasi-abstract machines. They are stack machines with
memories. *)


(** The stack in our machines is used both for regular data and for
recording function calls. In order to prevent invalid information
flows, we need to treat these two cases differently. Thus, a stack
element [StkElmt] is either a regular piece of data, tagged by
[AData], or a return address, tagged by [ARet]. The additional [bool]
parameter in [ARet] records whether a function is expected to return a
value or not, which is needed to prevent information leaks through the
stack layout. *)

Inductive StkElmt {T:Type} := 
| AData : @Atom T -> @StkElmt T
| ARet : @Atom T -> bool -> @StkElmt T.

(** [AS] is the type of states for the abstract and symbolic rule
machines. It is parametric over the type used for the labels on
atoms. *)

Record AS {T: Type}  := AState {
  amem : list (@Atom T);   (** The data memory. Its size is fixed during execution. *)
  aimem : list Instr;   (** The instruction memory. Doesn't change during execution. *)
  astk : list (@StkElmt T);  (** Stack *)
  apc : @Atom T  (** Program counter *)
}.

(** When stepping, the machines may output an [Event] *)
Inductive Event {T: Type} :=
| EInt : @Atom T -> @Event T.

Hint Resolve flows_refl flows_join_right flows_join_left : core.

Section ARuleMachine.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

(** [pop_to_return stk1 stk2] expresses that [stk2] is obtained from
[stk1] by popping all the data items off the top of [stk1], stopping
when a return address is found. It is used to define the semantics of
the return instructions. *)

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
