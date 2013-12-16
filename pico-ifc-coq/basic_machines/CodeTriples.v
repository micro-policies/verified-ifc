
Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import LibTactics.
Import ListNotations. 

Require Import Instr.
Require Import Lattices.
Require Import Concrete.
Require Import CodeGen.
Require Import ConcreteMachine.
Require Import Coq.Arith.Compare_dec.
Require Import ConcreteExecutions.
Require Import Semantics.

(** Generic tools for proving properties of (privileged) concrete machine code. *)

(** Tactic to automate proofs *)
Ltac split_vc := 
  (simpl; 
   match goal with 
   | H: exists X,_ |- _ => (destruct H; split_vc)
   | H: ?P /\ ?Q |- _ => (destruct H; split_vc)
   | |- forall P, _ => (intro; try subst; split_vc)
   | |- exists X, _ => (eexists; split_vc)
   | |- ?P /\ ?Q => (split; [(eauto; try (zify; omega);fail) | split_vc])
   | _ => (eauto; try (zify; omega))
   end).

(** * Definition of Hoare Triples *)
Section CodeTriples.
Local Open Scope Z_scope.

Definition imemory : Type := list Instr.
Definition memory : Type := list (@Atom Z). 
Definition stack : Type := list CStkElmt.
Definition code := list Instr.
Definition state := CS.

(** Instruction memory [im] contains code [c] starting at address [pc]. *)
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
  
(** Conditions for Hoare triples. The kernel code we consider only
changes the kernel memory and the stack, so our conditions consider
only these two components. *)

Definition HProp := memory -> stack -> Prop.


(** ** Hoare Triples for contained code *)

(** Hoare triple for a list of instructions executing only in kernel
mode. This is a total-correctness triple: if some kernel state
satisfies precondition [P] at the beginning of code [c], then it will
reach the end of [c] in some state that satisfies postcondition [Q],
while still being in kernel mode. Below are a series of lemmas about
this first kind of hoare triple. *)

Definition HT (c: code) (P Q: HProp) := 
  forall imem mem stk0 cache0 fh n n',
    code_at n fh c ->
    P cache0 stk0 ->
    n' = n + Z_of_nat (length c) -> 
    exists stk1 cache1,
      Q cache1 stk1 /\
      runsToEnd (CState cache0 mem fh imem stk0 (n, handlerTag) true)
                (CState cache1 mem fh imem stk1 (n', handlerTag) true).

Lemma HT_compose: forall c1 c2 P Q R,
  HT   c1 P Q ->
  HT   c2 Q R ->
  HT   (c1 ++ c2) P R.
Proof.
  unfold HT   in *.
  intros c1 c2 P Q R HT1 HT2 imem mem0 stk0 cache0 fh0 n n' HC12 HP Hn'.
  subst.
  
  edestruct HT1 as [stk1 [cache1 [HQ RTE1]]]; eauto.
  apply code_at_compose_1 in HC12; eauto.

  edestruct HT2 as [stk2 [cache2 [HR RTE2]]]; eauto.
  apply code_at_compose_2 in HC12; eauto.

  eexists. eexists. intuition. eauto.
  replace (@nil CEvent) with (@nil CEvent++@nil CEvent) by reflexivity.
  eapply runsToEnd_trans; eauto.

  let t := (rewrite app_length; zify; omega) in
  exact_f_equal RTE2; rec_f_equal t.
  
  (* let-binding necessary because 'tacarg's which are not 'id's or
     'term's need to be preceded by 'ltac' and enclosed in parens.
     E.g., the following works:

       exact_f_equal RTE2;
       rec_f_equal ltac:(rewrite app_length; zify; omega).

     See grammar at
     http://coq.inria.fr/distrib/8.4/refman/Reference-Manual012.html

   *)
Qed.

(** An alternate version of [HT_compose], which works better when unifying pre-conditions *)
Lemma HT_compose_bwd:
  forall (c1 c2 : code) (P Q R : HProp),
    HT c2 Q R -> HT c1 P Q -> HT (c1 ++ c2) P R.
Proof.
  intros; eapply HT_compose; eauto.
Qed.

Lemma HT_strengthen_premise: forall c (P' P Q: HProp),
  HT   c P  Q ->
  (forall m s, P' m s -> P m s) ->
  HT   c P' Q.
Proof.
  intros c P' P Q HTPQ P'__P.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP' Hn'.
  edestruct HTPQ as [mem2 [stk2 [HR RTE2]]]; eauto.
Qed.

Lemma HT_weaken_conclusion: forall c (P Q Q': HProp),
  HT   c P  Q ->
  (forall m s, Q m s -> Q' m s) ->
  HT   c P Q'.
Proof.
  intros ? ? ? ? HTPQ ?.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP' Hn'.
  edestruct HTPQ as [stk2 [c2 [HR RTE2]]]; eauto.
Qed.

Lemma HT_consequence: forall c (P' P Q Q': HProp),
  HT   c P Q ->
  (forall m s, P' m s -> P m s) ->
  (forall m s, Q m s -> Q' m s) ->
  HT   c P' Q'.
Proof.
  intros.
  eapply HT_weaken_conclusion; eauto.
  eapply HT_strengthen_premise; eauto.
Qed.

(** A strengthened rule of consequence that takes into account that [Q]
   need only be provable under the assumption that [P] is true for
   *some* state.  This lets us utilize any "pure" content in [P] when
   establishing [Q]. *)
Lemma HT_consequence': forall c (P' P Q Q': HProp),
  HT   c P Q ->
  (forall m s, P' m s -> P m s) ->
  (forall m s, (exists m' s', P' m' s') -> Q m s -> Q' m s) ->
  HT   c P' Q'.
Proof.
  intros ? ? ? ? ? HTPQ HPP' HP'QQ'.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP' Hn'.
  edestruct HTPQ as [stk2 [c2 [HR RTE2]]]; eauto.
  eexists. eexists. eexists.
  intuition.
  eapply HP'QQ'; eauto.
  eauto.
Qed.

Lemma HT_decide_join: forall T (v: T) c c1 c2 P1 P2 P1' P2' Q (D: T -> Prop),
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
  pose (decD v) as dec. intuition.
Qed.

Lemma HT_fold_constant_premise: forall (C:Prop) c P Q ,
  (C -> HT c P Q) ->
  HT c (fun m s => C /\ P m s) Q.
Proof.
  unfold HT.
  iauto.
Qed.

(** Hoare triples are implications, and so the following lemma correspond to
   the quantifier juggling lemma: (forall x, (P x -> Q)) <-> ((exists x, P x) -> Q)
*)
Lemma HT_forall_exists: forall T c P Q,
  (forall (x:T), HT   c (P x) Q) ->
  HT   c (fun m s => exists (x:T), P x m s) Q.
Proof.
  intros ? c P Q HPQ.
  unfold HT.
  intros imem mem0 stk0 c0 fh0 n n' Hcode_at [x HPx] neq.
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

(* The other direction is provable from [HT_strengthen_premise] *)
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


(** ** Hoare Triples with ghost variables *)

Definition GProp := memory -> stack -> HProp.

(** Ghost prop Hoare triple *)
Definition GT (c: code) (P: HProp) (Q: GProp) := forall m0 s0,
  HT c (fun m s => P m0 s0 /\ m = m0 /\ s = s0)
       (Q m0 s0).

Lemma GT_consequence':
  forall (c : code) (P' P: HProp) (Q Q': GProp),
    GT c P Q ->
    (forall m s, P' m s -> P m s) ->
    (forall m0 s0 m s, P m0 s0 -> Q m0 s0 m s -> Q' m0 s0 m s) ->
    GT c P' Q'.
Proof.
  unfold GT; intros.
  eapply HT_consequence'; jauto.
Qed.


(** ** Escaping Hoare Triples *)
(** We now define a different triple, [HTEscape]. The difference when
compared to [HT] is that instead of an execution ending necessarily in
kernel mode, we now specify cases where the machine successfully
returns to user mode at some known pc value or simply halts in kernel
mode before reaching the end. This is the triple we use to specify the
complete behavior of the fault handler. *)

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
:= forall imem mem stk0 cache0 fh n,
  code_at n fh c ->
  P cache0 stk0 ->
  exists stk1 cache1 pc1 priv1,
  let (prop, outcome) := Q cache1 stk1 in
  prop /\
  predicted_outcome outcome raddr pc1 priv1 /\
  runsToEscape
    (CState cache0 mem fh imem stk0 (n, handlerTag) true)
    (CState cache1 mem fh imem stk1 pc1 priv1).


Lemma HTEscape_strengthen_premise: forall r c (P' P: HProp) Q,
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

Lemma HTEscape_append: forall r c1 c2 P Q,
  HTEscape r c1 P Q ->
  HTEscape r (c1 ++ c2) P Q.
Proof.
  unfold HTEscape.
  intros.
  exploit code_at_compose_1; eauto.
Qed.

Definition HFun  := memory -> stack -> Z.


End CodeTriples.
