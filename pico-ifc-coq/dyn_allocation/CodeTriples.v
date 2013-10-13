(* Definitions and generic properties of Hoare triples for proofs on (privileged) machine code. *)

Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import LibTactics.
Import ListNotations.

Require Import Memory.
Require Import Instr.
Require Import Lattices.
Require Import Concrete.
Require Import CodeGen.
Require Import Concrete.
Require Import ConcreteExecutions.
Require Import ConcreteMachine.
Require Import Coq.Arith.Compare_dec.


Section Triples.
Local Open Scope Z_scope.

Variable cblock : block privilege.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.
Variable table : CSysTable.

Notation cstep := (cstep cblock).
Notation runsToEscape := (runsToEscape cblock).

Definition imemory : Type := list Instr.
Definition memory : Type := memory (val privilege) privilege.
Definition stack : Type := list CStkElmt.
Definition code := list Instr.
Definition state := CS.

(* ---------------------------------------------------------------- *)
(* Specs for self-contained code *)

(* ================================================================ *)
(* Hoare Triples *)

(* Instruction memory contains code [c] starting at address [pc]. *)
Fixpoint code_at (pc: Z) (im: imemory) (c: code): Prop :=
  match c with
  | nil     => True
  | i :: c' => index_list_Z pc im = Some i
               /\ code_at (pc + 1) im c'
  end.

Lemma code_at_compose_1: forall im c1 c2 n,
  code_at n im (c1 ++ c2) ->
  code_at n im c1.
Proof.
  induction c1; intros; simpl in *.
  intuition.
  intuition. eapply IHc1. eauto.
Qed.

Lemma code_at_compose_2: forall im c1 c2 n,
  code_at n im (c1 ++ c2) ->
  code_at (n + Z_of_nat (length c1)) im c2.
Proof.
  induction c1; intros; simpl in *.

  exact_f_equal H; omega.

  intuition.
  apply_f_equal IHc1; eauto; zify; omega.
Qed.

Lemma code_at_app : forall c2 c1 n,
  n = Z_of_nat (length c1) ->
  code_at n (c1 ++ c2) c2.
Proof.
  induction c2; intros.
  simpl. auto.
  simpl.
  split.
  rewrite index_list_Z_app. auto.
  subst n; auto.
  replace (c1 ++ a :: c2) with ((c1 ++ [a]) ++ c2).
  eapply IHc2.
  rewrite app_length. simpl. subst n; auto.
  zify; omega.
  rewrite app_ass. auto.
Qed.

Lemma code_at_id : forall c, code_at 0%Z c c.
Proof.
  intros. pattern c at 1.  replace c with ([]++c) by auto.
  eapply code_at_app.
  auto.
Qed.

(* Hoare triple for a list of instructions *)
Definition HT   (c: code)
                (P: memory -> stack -> Prop) (* pre-condition *)
                (Q: memory -> stack -> Prop) (* post-condition when code "falls through" *)
:= forall imem stk0 mem0 fh n n',
  code_at n fh c ->
  P mem0 stk0 ->
  n' = n + Z_of_nat (length c) ->
  exists stk1 mem1,
  Q mem1 stk1 /\
  runsToEnd cblock table
             (CState mem0 fh imem stk0 (n, handlerTag) true)
             (CState mem1 fh imem stk1 (n', handlerTag) true).

Inductive Outcome :=
| Success
| Failure.

Definition predicted_outcome (o: Outcome) raddr pc priv :=
  match o with
  | Success => priv = false /\ pc = raddr
  | Failure => priv = true  /\ pc = (-1, handlerTag)
  end.

Definition HTEscape raddr
  (c: code)
  (P: memory -> stack -> Prop)
  (Q: memory -> stack -> Prop * Outcome)
:= forall imem stk0 mem0 fh n,
  code_at n fh c ->
  P mem0 stk0 ->
  exists stk1 mem1 pc1 priv1,
  let (prop, outcome) := Q mem1 stk1 in
  prop /\
  predicted_outcome outcome raddr pc1 priv1 /\
  runsToEscape table
    (CState mem0 fh imem stk0 (n, handlerTag) true)
    (CState mem1 fh imem stk1 pc1 priv1).

Lemma HTEscape_strengthen_premise: forall r c (P' P: memory -> stack -> Prop) Q,
  HTEscape r c P  Q ->
  (forall m s, P' m s -> P m s) ->
  HTEscape r c P' Q.
Proof.
  introv HTPQ P'__P.
  unfold HTEscape; intros.
  edestruct HTPQ as [mem2 [stk2 [HR RTE2]]]; eauto.
Qed.

Lemma HTEscape_compose: forall r c1 c2 P Q R,
  HT         c1 P Q ->
  HTEscape r c2 Q R ->
  HTEscape r (c1 ++ c2) P R.
Proof.
  introv H_HT H_HTE.
  intro; intros.

  edestruct H_HT as [cache1 [stk1 [HQ Hstar1]]]; eauto.
  eapply code_at_compose_1; eauto.

  edestruct H_HTE as [stk2 [cache2 [pc2 [priv2 Hlet]]]]; eauto.
  eapply code_at_compose_2; eauto.

  exists stk2 cache2 pc2 priv2.
  destruct (R cache2 stk2).
  destruct Hlet as [? [Houtcome ?]].
  destruct o; unfold predicted_outcome in Houtcome; simpl; intuition; subst.
  - eapply rte_success.
    eapply runsUntilUser_trans; eauto.
    inv H2; eauto.
    apply runsToEnd_r in STAR.
    simpl in STAR. congruence.
  - eapply rte_fail.
    eapply runsToEnd_trans; eauto.
    inv H2; eauto.
    + apply runsUntilUser_r in STAR.
      simpl in STAR. congruence.
    + simpl. omega.
Qed.

Lemma HTEscape_compose_flip: forall r c1 c2 P Q R,
    HTEscape r c2 Q R ->
    HT c1 P Q ->
    HTEscape r (c1 ++ c2) P R.
Proof.
  intros. eapply HTEscape_compose; eauto.
Qed.

Lemma HTEscape_append: forall r c1 c2 P Q,
  HTEscape r c1 P Q ->
  HTEscape r (c1 ++ c2) P Q.
Proof.
  unfold HTEscape.
  intros.
  exploit code_at_compose_1; eauto.
Qed.

Lemma HT_compose: forall c1 c2 P Q R,
  HT   c1 P Q ->
  HT   c2 Q R ->
  HT   (c1 ++ c2) P R.
Proof.
  unfold HT   in *.
  intros c1 c2 P Q R HT1 HT2 imem stk0 mem0 fh0 n n' HC12 HP Hn'.
  subst.

  edestruct HT1 as [stk1 [mem1 [HQ RTE1]]]; eauto.
  apply code_at_compose_1 in HC12; eauto.

  edestruct HT2 as [stk2 [mem2 [HR RTE2]]]; eauto.
  apply code_at_compose_2 in HC12; eauto.

  eexists. eexists. intuition. eauto.
  replace (@nil CEvent) with (@nil CEvent++@nil CEvent) by reflexivity.
  eapply runsToEnd_trans; eauto.

  (* NC: why is this let-binding necessary ? *)
  let t := (rewrite app_length; zify; omega) in
  exact_f_equal RTE2; rec_f_equal t.
  (* Because 'tacarg's which are not 'id's or 'term's need to be
     preceded by 'ltac' and enclosed in parens.  E.g., the following
     works:

       exact_f_equal RTE2;
       rec_f_equal ltac:(rewrite app_length; zify; omega).

     See grammar at
     http://coq.inria.fr/distrib/8.4/refman/Reference-Manual012.html

   *)
Qed.

(* An alternate version, which works better when unifying pre-conditions *)
Lemma HT_compose_flip : forall c1 c2 P Q R,
                      HT c2 Q R ->
                      HT c1 P Q ->
                      HT (c1 ++ c2) P R.
Proof. intros. eauto using HT_compose. Qed.

Lemma HTEscape_weaken_conclusion: forall r c P (Q Q': memory -> stack -> Prop * Outcome),
  HTEscape r c P Q ->
  (forall m s, fst (Q m s) -> fst (Q' m s)) ->
  (forall m s, snd (Q m s) = snd (Q' m s)) ->
  HTEscape r c P Q'.
Proof.
  intros r c P Q Q' HTPQ Q__Q' O__O'.
  unfold HTEscape; intros.
  unfold HTEscape in HTPQ.
  edestruct HTPQ; eauto.
  destruct H1 as [mem2 [pc2 [priv2 HH]]].
  case_eq (Q mem2 x); intros. rewrite H1 in *.
  destruct HH as [HP0 [HOUT RTE]].
  exists x ; exists mem2; exists pc2 ; exists priv2.
  case_eq (Q' mem2 x); intros. intuition.
  replace P1 with (fst (Q' mem2 x)); [ | rewrite H2 ; eauto].
  eapply Q__Q'; eauto.
  rewrite H1; auto.
  unfold predicted_outcome in HOUT.
  {
  cases o; cases o0; subst; intuition.
    - constructor; auto.
    - assert (HCONT:= O__O' mem2 x); eauto.
      rewrite H1 in HCONT. rewrite H2 in HCONT. inv HCONT.
    - assert (HCONT:= O__O' mem2 x); eauto.
      rewrite H1 in HCONT. rewrite H2 in HCONT. inv HCONT.
    - constructor; auto.
  }
 eapply RTE.
Qed.

Lemma HTEscape_forall_exists : forall (T : Type) c pc
         (P : T -> memory -> stack -> Prop) (Q : memory -> stack -> Prop * Outcome),
       (forall x : T, HTEscape pc c (P x) Q) ->
       HTEscape pc c (fun (m : memory) (s : stack) => exists x, P x m s) Q.
Proof.
  intros.
  unfold HTEscape.
  intros imem mem0 stk0 fh0 n0 Hcode_at [x HPx].
  eapply H; eauto.
Qed.

(* ================================================================ *)
(* Lemmas on Hoare Triples *)

Lemma HT_strengthen_premise: forall c (P' P Q: memory -> stack -> Prop),
  HT   c P  Q ->
  (forall m s, P' m s -> P m s) ->
  HT   c P' Q.
Proof.
  intros c P' P Q HTPQ P'__P.
  intros imem mem0 stk0 fh0 n n' Hcode HP' Hn'.
  edestruct HTPQ as [mem2 [stk2 [HR RTE2]]]; eauto.
Qed.

Lemma HT_weaken_conclusion: forall c (P Q Q': memory -> stack -> Prop),
  HT   c P  Q ->
  (forall m s, Q m s -> Q' m s) ->
  HT   c P Q'.
Proof.
  intros ? ? ? ? HTPQ ?.
  intros imem mem0 stk0 fh0 n n' Hcode HP' Hn'.
  edestruct HTPQ as [stk2 [c2 [HR RTE2]]]; eauto.
Qed.

Lemma HT_consequence: forall c (P' P Q Q': memory -> stack -> Prop),
  HT   c P Q ->
  (forall m s, P' m s -> P m s) ->
  (forall m s, Q m s -> Q' m s) ->
  HT   c P' Q'.
Proof.
  intros.
  eapply HT_weaken_conclusion; eauto.
  eapply HT_strengthen_premise; eauto.
Qed.

(* A strengthened rule of consequence that takes into account that [Q]
   need only be provable under the assumption that [P] is true for
   *some* state.  This lets us utilize any "pure" content in [P] when
   establishing [Q]. *)
Lemma HT_consequence': forall c (P' P Q Q': memory -> stack -> Prop),
  HT   c P Q ->
  (forall m s, P' m s -> P m s) ->
  (forall m s, (exists m' s', P' m' s') -> Q m s -> Q' m s) ->
  HT   c P' Q'.
Proof.
  intros ? ? ? ? ? HTPQ HPP' HP'QQ'.
  intros imem mem0 stk0 fh0 n n' Hcode HP' Hn'.
  edestruct HTPQ as [stk2 [c2 [HR RTE2]]]; eauto.
  eexists. eexists. eexists.
  intuition.
  eapply HP'QQ'; eauto.
  eauto.
Qed.

Lemma HT_decide_join: forall T c c1 c2 P1 P2 P1' P2' Q (D: T -> Prop),
  (forall v, HT   c1 P1 Q -> ~ D v -> HT   c (P1' v) Q) ->
  (forall v, HT   c2 P2 Q ->   D v -> HT   c (P2' v) Q) ->
  (forall v, ~ D v \/ D v) ->
  HT   c1 P1 Q ->
  HT   c2 P2 Q ->
  HT   c (fun m s => exists v, (~ D v /\ P1' v m s) \/ (D v /\ P2' v m s)) Q.
Proof.
  intros ? c c1 c2 P1 P2 P1' P2' Q D spec1 spec2 decD HT1 HT2.
  unfold HT. intros imem mem0 stk0 fh0 n n' H_code_at HP neq.
  destruct HP as [v Htovornottov].
  pose (decD v) as dec. intuition.

  eapply spec1; eauto.
  eapply spec2; eauto.
Qed.

Lemma HT_decide_join': forall T (v: T) c c1 c2 P1 P2 P1' P2' Q (D: T -> Prop),
  (HT   c1 P1 Q -> ~ D v -> HT   c P1' Q) ->
  (HT   c2 P2 Q ->   D v -> HT   c P2' Q) ->
  (forall v, ~ D v \/ D v) ->
  HT   c1 P1 Q ->
  HT   c2 P2 Q ->
  (* Switched to implication here.  I think this is a weaker
     assumption, and it's closer to the form of the [ifNZ] spec I want
   *)
  HT   c (fun m s => (~ D v -> P1' m s) /\ (D v -> P2' m s)) Q.
Proof.
  intros ? v c c1 c2 P1 P2 P1' P2' Q D spec1 spec2 decD HT1 HT2.
  unfold HT. intros imem mem0 stk0 n n' H_code_at HP neq.
  (* destruct HP as [v [[HDv HP1'] | [HnDv HP2']]]. *)
  pose (decD v) as dec. intuition.
Qed.

(* Hoare triples are implications, and so this corresponds to the
   quantifier juggling lemma:

     (forall x, (P x -> Q)) ->
     ((exists x, P x) -> Q)

*)
Lemma HT_forall_exists: forall T c P Q,
  (forall (x:T), HT   c (P x) Q) ->
  HT   c (fun m s => exists (x:T), P x m s) Q.
Proof.
  intros ? c P Q HPQ.
  unfold HT.
  intros imem mem0 stk0 fh0 n n' Hcode_at [x HPx] neq.
  eapply HPQ; eauto.
(*
  (* Annoyingly, we can't use [HT_strengthen_premise] here, because
     the existential [x] in [exists (x:T), P x m s] is not introduced
     early enough :P.  I'm not alone:
     https://sympa.inria.fr/sympa/arc/coq-club/2013-01/msg00055.html *)
  intros ? c P Q HPQ.
  eapply HT_strengthen_premise.
  eapply HPQ.
  intros m s [x HPx].
  (* Error: Instance is not well-typed in the environment of ?14322 *)
  (* instantiate (1:=x). *)
  (* And similar problems with: *)
  (* exact HPx. *)
*)
Qed.

(* The other direction (which I don't need) is provable from
   [HT_strengthen_premise] *)
Lemma HT_exists_forall: forall T c P Q,
  HT   c (fun m s => exists (x:T), P x m s) Q ->
  (forall (x:T), HT   c (P x) Q).
Proof.
  intros ? c P Q HPQ x.
  eapply HT_strengthen_premise.
  eapply HPQ.
  intuition.
  eauto.
Qed.

Lemma HT_fold_constant_premise: forall (C:Prop) c P Q ,
  (C -> HT c P Q) ->
  HT c (fun m s => C /\ P m s) Q.
Proof.
  unfold HT.
  iauto.
Qed.

Definition Trans := (memory -> stack -> Prop) -> (memory -> stack -> Prop).

(* Transformer style *)
Definition HTT (c : code) (T : Trans) :=
  forall Q, HT c (T Q) Q.

Lemma HTT_strengthen_premise :
  forall c (T T' : Trans)
         (H : HTT c T)
         (STRENGTHEN : forall Q m s, T' Q m s -> T Q m s),
    HTT c T'.
Proof.
  intros. intro Q.
  eapply HT_strengthen_premise; eauto.
  eauto.
Qed.

Lemma HTT_compose :
  forall c1 c2 (T1 T2 : Trans)
         (HTT1 : HTT c1 T1)
         (HTT2 : HTT c2 T2),
    HTT (c1 ++ c2) (fun Q => T1 (T2 Q)).
Proof.
  intros.
  intros Q.
  eapply HT_compose; eauto.
Qed.

End Triples.
