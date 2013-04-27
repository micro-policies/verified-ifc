(* Generic tools for proving properties of (privileged) concrete machine code. *)

Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import LibTactics.
Import ListNotations. 

Require Import TMUInstr.
Require Import Lattices.
Require Import Concrete.
Require Import CodeGen.
Require Import ConcreteMachineSmallStep.
Require Import Determinism.
Require Import Coq.Arith.Compare_dec.

Section CodeSpecs.
Local Open Scope Z_scope.

Definition imemory : Type := list Instr.
Definition memory : Type := list (@Atom Z). 
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

(* Self contained code: [runsToEnd pc1 pc2 cs1 cs2] starts at pc2
[pc1] and runs until pc [pc2]. *)
Inductive runsToEnd (Rstep: CS -> option CEvent -> CS -> Prop) : Z -> Z -> CS -> list CEvent -> CS -> Prop :=
| runsToEndDone : forall n cs,
  fst (pc cs) = n -> 
  runsToEnd Rstep n n cs nil cs
  (* NC: do we need to worry about [n <= n' <= n'']? *)
| runsToEndStep: forall n n' n'' cs e cs' t cs'',
  fst (pc cs) = n ->
  Rstep cs e cs' ->
  fst (pc cs') = n' ->
  (* DD: I just comment out these for now, as the new hyp breaks composition lemma below *)
  (* n <> n'' ->  *)  n < n'' -> (* BEFORE: n < n' -> *) 
  runsToEnd Rstep n' n'' cs' t cs'' -> 
  runsToEnd Rstep n  n'' cs  (op_cons e t) cs''.

(* APT: With second option above ( n < n'') it is
   easy enough to prove the following two lemmas.
   But at the moment, Nathan and I don't see any
   strong reason to include this restriction...
*)
Lemma runsToEnd_bounded: forall step pc0 pc1 s0 s1 t, 
  runsToEnd step pc0 pc1 s0 t s1 -> pc0 <= pc1. 
Proof.
  intros.  inv H; omega.
Qed.

Lemma runsToEnd_compose : forall step pc0 pc1 s0 t1 s1,
  runsToEnd step pc0 pc1 s0 t1 s1 ->
  forall pc2 s2 t2,
  runsToEnd step pc1 pc2 s1 t2 s2 ->
  runsToEnd step pc0 pc2 s0 (t1++t2) s2.
Proof.
  induction 1. 
  intros; simpl; auto.
  intros. 
  rewrite op_cons_app. econstructor; eauto.
  apply runsToEnd_bounded in H4. 
  omega.
Qed.

Lemma runsToEnd_determ : forall (step : CS -> option CEvent -> CS -> Prop) pc0 pc1 s0 t1 s1 s1',
  forall (STEP_DET: forall s e s' e' s'', step s e s' -> step s e' s'' -> s' = s'' /\ e = e') ,
  runsToEnd step pc0 pc1 s0 t1 s1 ->
  forall t2, runsToEnd step pc0 pc1 s0 t2 s1' ->
  s1 = s1' /\ t1 = t2.
Proof.
  intros until 1. 
  induction 1; intros.
    inv H0. 
      auto.
      exfalso; omega. 
    inv H4.
      exfalso; omega. 
      assert (cs' = cs'0) by (eapply STEP_DET; eauto). 
      assert (e = e0) by (eapply STEP_DET; eauto). subst.
      exploit IHrunsToEnd; eauto. intros [Heq Heq'].
      subst. split; eauto.
Qed.
  
(*
Lemma runsToEnd_compose : forall step pc0 pc1 s0 s1,
  runsToEnd step pc0 pc1 s0 s1 ->
  forall pc2 s2,
  runsToEnd step pc1 pc2 s1 s2 ->
  runsToEnd step pc0 pc2 s0 s2.
Proof.
  induction 1. 
  intros; auto.
  intros. 
  econstructor; eauto.
Qed.
*)

(* Hoare triple for a list of instructions *)
Definition HT   (c: code)
                (P: memory -> stack -> Prop) (* pre-condition *)
                (Q: memory -> stack -> Prop) (* post-condition when code "falls through" *)
:= forall imem mem stk0 cache0 fh n n',
  code_at n fh c ->
  P cache0 stk0 ->
  n' = n + Z_of_nat (length c) -> 
  exists stk1 cache1,
  Q cache1 stk1 /\
  runsToEnd cstep n n' 
             (CState cache0 mem fh imem stk0 (n, handlerTag) true)
             nil 
             (CState cache1 mem fh imem stk1 (n', handlerTag) true).

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
    nil
    (CState cache1 mem fh imem stk1 pc1             priv1).

Lemma HTEscape_strengthen_premise: forall r c (P' P: memory -> stack -> Prop) Q,
  HTEscape r c P  Q ->
  (forall m s, P' m s -> P m s) ->
  HTEscape r c P' Q.
Proof.
  introv HTPQ P'__P.
  unfold HTEscape; intros.
  edestruct HTPQ as [mem2 [stk2 [HR RTE2]]]; eauto.
Qed.

Lemma runsToEnd_star: forall n1 n2 s1 t s2,
  runsToEnd cstep n1 n2 s1 t s2 ->
  star cstep s1 t s2.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma HT_star: forall c P Q,
  HT c P Q ->
  forall imem mem stk0 cache0 fh n n',
  code_at n fh c ->
  P cache0 stk0 ->
  n' = n + Z_of_nat (length c) ->
  exists cache1 stk1,
  Q cache1 stk1 /\
  star cstep (CState cache0 mem fh imem stk0 (n, handlerTag) true)
             nil
             (CState cache1 mem fh imem stk1 (n', handlerTag) true).
Proof.
  unfold HT.
  introv HTcPQ; intros.
  edestruct HTcPQ as [stk2 [cache2 [HQ RTE2]]]; eauto; clear HTcPQ.
  repeat eexists; eauto.
  eapply runsToEnd_star; eauto.
Qed.

Lemma HTEscape_star: forall raddr c P Q,
  HTEscape raddr c P Q ->
  forall imem mem stk0 cache0 fh n,
  code_at n fh c ->
  P cache0 stk0 ->
  exists stk1 cache1 pc1 priv1,
  let (prop, outcome) := Q cache1 stk1 in
  prop /\
  predicted_outcome outcome raddr pc1 priv1 /\
  star cstep
    (CState cache0 mem fh imem stk0 (n, handlerTag) true)
    nil
    (CState cache1 mem fh imem stk1 pc1             priv1).
Proof.
  unfold HTEscape.
  introv HTcPQ; intros.
  edestruct HTcPQ as [stk1 [cache1 [pc1 [priv1 RTE2]]]]; eauto; clear HTcPQ.
  exists stk1 cache1 pc1 priv1.
  destruct (Q cache1 stk1); intuition.
  eapply runsToEscape_star; eauto.
Qed.

Lemma HTEscape_compose: forall r c1 c2 P Q R,
  HT         c1 P Q ->
  HTEscape r c2 Q R ->
  HTEscape r (c1 ++ c2) P R.
Proof.
  introv H_HT H_HTE.
  intro; intros.

  edestruct (HT_star _ _ _ H_HT) as [cache1 [stk1 [HQ Hstar1]]]; eauto.
  eapply code_at_compose_1; eauto.

  edestruct (HTEscape_star _ _ _ _ H_HTE) as [stk2 [cache2 [pc2 [priv2 Hlet]]]]; eauto.
  eapply code_at_compose_2; eauto.

  exists stk2 cache2 pc2 priv2.
  destruct (R cache2 stk2).
  destruct Hlet as [? [Houtcome ?]].
  destruct o; unfold predicted_outcome in Houtcome; simpl; intuition; subst.
  - eapply rte_success.
    + reflexivity.
    + eapply star_trans with (t:=[]) (t':=[]); eauto.
    + reflexivity.
  - eapply rte_fail.
    + reflexivity.
    + eapply star_trans with (t:=[]) (t':=[]); eauto.
    + reflexivity.
    + simpl; omega.
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
  intros c1 c2 P Q R HT1 HT2 imem mem0 stk0 cache0 fh0 n n' HC12 HP Hn'.
  subst.
  
  edestruct HT1 as [stk1 [cache1 [HQ RTE1]]]; eauto.
  apply code_at_compose_1 in HC12; eauto.

  edestruct HT2 as [stk2 [cache2 [HR RTE2]]]; eauto.
  apply code_at_compose_2 in HC12; eauto.

  eexists. eexists. intuition. eauto.
  replace (@nil CEvent) with (@nil CEvent++@nil CEvent) by reflexivity.
  eapply runsToEnd_compose; eauto.

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


(* ================================================================ *)
(* Lemmas on Hoare Triples *)

Lemma HT_strengthen_premise: forall c (P' P Q: memory -> stack -> Prop),
  HT   c P  Q ->
  (forall m s, P' m s -> P m s) ->
  HT   c P' Q.
Proof.
  intros c P' P Q HTPQ P'__P.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP' Hn'.
  edestruct HTPQ as [mem2 [stk2 [HR RTE2]]]; eauto.
Qed.

Lemma HT_weaken_conclusion: forall c (P Q Q': memory -> stack -> Prop),
  HT   c P  Q ->
  (forall m s, Q m s -> Q' m s) ->
  HT   c P Q'.
Proof.
  intros ? ? ? ? HTPQ ?.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP' Hn'.
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
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP' Hn'.
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
  unfold HT. intros imem mem0 stk0 c0 fh0 n n' H_code_at HP neq.
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

Lemma HT_split_conclusion: forall c (P Q Q': memory -> stack -> Prop),
  HT c P Q ->
  HT c P Q' ->
  HT c P (fun m s => Q m s /\ Q' m s).
Proof.
  intros.
  unfold HT in *. intros.
  edestruct (H imem mem) as [sk [cache [HQ R]]]. eapply H1.  eapply H2. eapply H3. 
  edestruct (H0 imem mem) as [sk' [cache' [HQ' R']]]; eauto.
  exists sk. exists cache.
  pose proof (@runsToEnd_determ cstep _ _ _ _ _ _ cmach_priv_determ_state R _ R').
  inv H4. inv H5.
  intuition.
Qed.

(* ================================================================ *)
(* Specs for concrete code *)

Ltac nil_help :=   replace (@nil CEvent) with (op_cons None (@nil CEvent)) by reflexivity.

(* Simplest example: the specification of a single instruction run in
privileged mode *)
Lemma add_spec: forall (z1 z2: Z) (l1 l2: Z) (m: memory) (s: stack),
  HT  [Add]
      (fun m1 s1 => m1 = m /\ s1 = CData (z1,l1) :: CData (z2,l2) :: s)
      (fun m2 s2 => m2 = m /\ s2 = CData (z1 + z2, handlerTag) :: s).
Proof.
  (* Introduce hyps *)
  intros.
  unfold HT. intros. intuition.
  eexists.
  eexists.
  eexists.
  intuition. 

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. intuition. 
  
  (* Run an instruction *)
  nil_help.
  eapply runsToEndStep; auto.
  eapply cstep_add_p ; eauto.
  omega.
  
  (* Finish running *)
  eapply runsToEndDone; auto.
Qed.

Lemma add_sub_spec: forall (z1 z2: Z) (l1 l2: Z) (m: memory) (s: stack),
  HT   (Add :: Sub :: nil)
      (fun m1 s1 => m1 = m /\ s1 = CData (z1,l1) :: CData (z2,l2) :: CData (z2,l2) :: s)
      (fun m2 s2 => m2 = m /\ s2 = CData (z1, handlerTag) :: s).
Proof.
  (* Introduce hyps *)
  intros.
  unfold HT. intros. intuition. subst. 
  eexists.
  eexists.
  eexists.
  intuition. 

  (* Load an instruction *)
  simpl.
  unfold code_at in *. intuition. 
  
  (* Run an instruction *)
  nil_help.
  eapply runsToEndStep; auto.
  eapply cstep_add_p; eauto.
  omega. 
  
  (* Run an instruction *)
  nil_help.
  eapply runsToEndStep; auto.
  eapply cstep_sub_p; eauto.
  simpl; omega. 

  (* Finish running *)
  let t := (auto || simpl; omega) in
  apply_f_equal @runsToEndDone; rec_f_equal t.
Qed.

Lemma sub_spec: forall z1 l1 z2 l2, forall m0 s0,
  HT [Sub]
     (fun m s => m = m0 /\ s = (z1,l1) ::: (z2,l2) ::: s0)
     (fun m s => m = m0 /\ s = (z1 - z2,handlerTag) ::: s0).
Proof.
  unfold HT; intros.
  eexists.
  eexists.
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  nil_help. eapply runsToEndStep; auto.
  eapply cstep_sub_p; eauto.
  omega.
  simpl.
  constructor; auto.
Qed.

Lemma push_spec: forall v P,
  HT   (Push v :: nil)
       (fun m s => P m (CData (v,handlerTag) :: s))
       P.
Proof.
  intros v P.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP Hn'.
  eexists. eexists. intuition. eauto.
  
  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. simpl in *. intuition. 

  (* Run an instruction *)
  nil_help. eapply runsToEndStep; auto.
  eapply cstep_push_p ; eauto.
  omega. 
  simpl.
  constructor; auto.
Qed.

Lemma push_spec': forall v P,
  HT   (Push v :: nil)
       P
       (fun m s => head s = Some (CData (v,handlerTag)) /\
                            P m (tail s)).
Proof.
  intros v P.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP Hn'.
  exists (CData (v, handlerTag) :: stk0). eexists c0.
  intuition.
  
  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. intuition. 

  (* Run an instruction *)
  nil_help.
  eapply runsToEndStep; auto.
  eapply cstep_push_p ; eauto.
  omega. 
  simpl.
  constructor; auto.
Qed.

(* Ghost variable style *)
(* NC: to write a generic instruction-verification tactic, it seems we
   may only need to factor out the specific unfoldings (here [push'])
   and the specific step lemmas (here [cp_push]). *)
Lemma push_spec'': forall v, forall m0 s0,
  HT (push' v)
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = CData (v,handlerTag) :: s0).
Proof.
  intros.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP' Hn'.
  eexists.
  eexists.
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold push', code_at in *. intuition.

  (* Run an instruction *)
  nil_help.
  eapply runsToEndStep; auto.
  eapply cstep_push_p; eauto.
  omega. 
  simpl.
  constructor; auto.
Qed.

Lemma load_spec: forall a al v vl, forall m0 s0,
  index_list_Z a m0 = Some (v,vl) ->
  HT [Load]
     (fun m s => m = m0 /\ s = CData (a,al) :: s0)
     (fun m s => m = m0 /\ s = CData (v,handlerTag) :: s0).
Proof.
  intros a al v vl m0 s0  Hmem.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP' Hn'.
  eexists.
  eexists.
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. intuition. 

  (* Run an instruction *)
  nil_help. eapply runsToEndStep; auto.
  eapply cstep_load_p; eauto.
  omega.
  simpl.
  constructor; auto.
Qed.

Lemma loadFrom_spec: forall a v vl, forall m0 s0,
  index_list_Z a m0 = Some (v,vl) ->
  HT (loadFrom a)
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = CData (v,handlerTag) :: s0).
Proof.
  intros.
  eapply HT_compose.
  eapply push_spec''.
  eapply load_spec.
  eauto.
Qed.

Lemma pop_spec: forall v vl, forall m0 s0,
  HT pop
     (fun m s => m = m0 /\ s = CData (v,vl) :: s0)
     (fun m s => m = m0 /\ s = s0).
Proof.
  unfold HT.
  intros.
  eexists.
  eexists.
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold pop, code_at in *. intuition.

  (* Run an instruction *)
  nil_help.
  eapply runsToEndStep; auto.
  eapply cstep_branchnz_p; eauto.
  omega.
  simpl.
  destruct (v =? 0); constructor; auto.
Qed.

Lemma nop_spec: forall m0 s0,
  HT nop
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = s0).
Proof.
  unfold HT.
  intros.
  exists s0.
  exists m0.
  intuition.
  simpl in H1; subst.
  apply_f_equal @runsToEndDone; rec_f_equal ltac:(try (zify; omega); auto).
Qed.


(* Move this to the place in Utils.v with related lemmas once it's
proven. *)
Section MoveThisToUtils.

Local Open Scope nat_scope.

Lemma update_list_Some (T': Type): forall (v: T') l n,
  n < length l ->
  exists l', update_list n v l = Some l'.
Proof.
  induction l; intros. 
  - inv H. 
  - destruct n. 
    + simpl.  eauto.
    + simpl. edestruct IHl as [l' E]. simpl in H. instantiate (1:= n). omega. 
      eexists. rewrite E. eauto.
Qed.

Lemma update_list_Z_Some (T':Type): forall (v:T') l (i:Z),
  (0 <= i)%Z ->
  Z.to_nat i < length l ->
  exists l', update_list_Z i v l = Some l'. 
Proof.
  intros. unfold upd_m. 
  destruct (i <? 0) eqn:?. 
  - rewrite Z.ltb_lt in Heqb. omega. 
  - eapply update_list_Some; eauto. 
Qed.

Lemma update_preserves_length: forall T a (vl:T) m m',
  update_list a vl m = Some m' ->
  length m' = length m.
Proof.
  induction a; intros.
  - destruct m; simpl in *.
    + false.
    + inversion H; subst; reflexivity.
  - destruct m; simpl in *.
    + false.
    + cases (update_list a vl m).
      * exploit IHa; eauto.
        inversion H; subst.
        intros eq; rewrite <- eq; reflexivity.
      * false.
Qed.

End MoveThisToUtils.

(* NC: to prove that addresses are valid per this definition, we just
   need to know that that the memory is at least as large as the
   [tmuCacheSize] defined in Concrete.v, since we only use
   [valid_address] assumptions for [addrTag*]. *)
Definition valid_address a (m: memory) :=
  (0 <= a) /\ (Z.to_nat a < length m)%nat.

Lemma valid_read: forall a m,
  valid_address a m ->
  exists v, read_m a m = Some v.
Proof.
  introv H.
  unfold valid_address in H.
  unfold read_m.
  cases (a <? 0).
  - false.
    rewrite Z.ltb_lt in Eq. omega.
  - remember (Z.to_nat a) as n; clear Heqn.
    destruct H as [_ Hbound].
    generalize dependent n.
    generalize dependent m.
    induction m; intros.
    + false; simpl in *; omega.
    + cases n; subst.
      * simpl; eauto.
      * simpl in Hbound.
        apply lt_S_n in Hbound.
        eauto.
Qed.

Lemma valid_store: forall a v m,
  valid_address a m ->
  exists m', upd_m a v m = Some m'.
Proof.
  intros.
  unfold valid_address in H. 
  eapply update_list_Z_Some; iauto.
Qed. 

Lemma store_spec: forall a al v vl m s,
  HT [Store]
     (fun m0 s0 => m0 = m /\
                   s0 = (a,al) ::: (v,vl) ::: s /\
                   valid_address a m) (* NC: better to move this outside? *)
     (fun m1 s1 => s1 = s /\
                   upd_m a (v,vl) m = Some m1).
Proof.
  unfold HT.
  intros.
  edestruct valid_store.
  iauto.
  eexists.
  eexists.
  intuition; subst.
  eauto.

  (* Load an instruction *)
  unfold code_at in *. intuition.

  (* Run an instruction *)
  nil_help. eapply runsToEndStep; auto.
  eapply cstep_store_p; eauto.
  simpl; omega.

  constructor; eauto.
Qed.

Lemma storeAt_spec: forall a v vl m s,
  HT (storeAt a)
     (fun m0 s0 => m0 = m /\
                   s0 = (v,vl) ::: s /\
                   valid_address a m)
     (fun m1 s1 => s1 = s /\
                   upd_m a (v,vl) m = Some m1).
Proof.
  intros.
  eapply HT_compose.
  eapply HT_consequence'.
  eapply push_spec''.
  intuition; eauto.
  intuition; eauto.
  Focus 2. (* Eeek! *)
  eapply store_spec.
  intuition; eauto.
  jauto.
Qed.

Lemma skipNZ_continuation_spec_NZ: forall c P v l,
  v <> 0 ->
  HT   (skipNZ (length c) ++ c)
       (fun m s => (exists s', s = CData (v,l) :: s' 
                               /\ P m s'))
       P.
Proof.
  intros c P v l Hv.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP Hn'.
  destruct HP as [stk1 [H_stkeq HPs']].
  exists stk1. exists c0. 
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. simpl in *. intuition. fold code_at in *.

  (* Run an instruction *) 
  nil_help. 
  eapply runsToEndStep; eauto. 
  eapply cstep_branchnz_p ; eauto. 
  zify ; omega.

  simpl. assert (Hif: v =? 0 = false) by (destruct v; [omega | auto | auto]).  
  rewrite Hif.
  constructor 1; auto.
Qed.

Lemma skipNZ_spec_Z: forall n P v l,
  v = 0 ->
  HT   (skipNZ n)
       (fun m s => (exists s', s = CData (v,l) :: s' 
                               /\ P m s'))
       P.
Proof.
  intros c P v l Hv.
  intros imem mem0 stk0 c0 fh n n' Hcode HP Hn'.
  destruct HP as [stk1 [H_stkeq HPs']].
  exists stk1. eexists c0.
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. simpl in *. 
  intuition. 

  (* Run an instruction *)
  nil_help. 
  eapply runsToEndStep; auto.
  eapply cstep_branchnz_p ; eauto. 
  omega.
  simpl.
  constructor; auto.
Qed.

Lemma skipNZ_continuation_spec_Z: forall c P Q v l,
  v = 0 ->
  HT   c P Q  ->
  HT   (skipNZ (length c) ++ c)
       (fun m s => (exists s', s = CData (v,l) :: s' 
                               /\ P m s'))
       Q.
Proof.
  intros c P Q v l Hv HTc.
  eapply HT_compose.
  eapply skipNZ_spec_Z; auto.
  auto.
Qed.

Lemma skip_spec: forall c P,
  HT   (skip (length c) ++ c)
       P
       P.
Proof.
  intros c P.
  unfold skip.
  rewrite app_ass.  
  eapply HT_compose.
  eapply push_spec'.
  eapply HT_strengthen_premise. 
  eapply skipNZ_continuation_spec_NZ with (v:= 1); omega.

  intros.
  simpl.
  exists (tl s); intuition.
  destruct s; inversion H0; eauto.
Qed.

Lemma ifNZ_spec_Z: forall v l t f P Q,
  HT   f P Q ->
  v = 0 ->
  HT   (ifNZ t f)
       (fun m s => (exists s', s = CData (v,l) :: s' /\ P m s'))
       Q.
Proof.
  intros v l t f P Q HTf Hveq0.
  unfold ifNZ.
  rewrite app_ass.
  eapply HT_compose.
  
  apply skipNZ_spec_Z; auto.

  eapply HT_compose; eauto.

  apply skip_spec.
Qed.

Lemma ifNZ_spec_NZ: forall v l t f P Q,
  HT   t P Q ->
  v <> 0 ->
  HT   (ifNZ t f)
       (fun m s => (exists s', s = CData (v,l) :: s' /\ P m s'))
       Q.
Proof.
  intros v l t f P Q HTt Hveq0.
  unfold ifNZ.
  rewrite <- app_ass.
  eapply HT_compose; eauto.
  apply skipNZ_continuation_spec_NZ; auto.
Qed.

Lemma ifNZ_spec_helper: forall v l t f Pt Pf Q,
  HT   t Pt Q ->
  HT   f Pf Q ->
  HT   (ifNZ t f)
       (fun m s => ((v <> 0 -> exists s', s = CData (v,l) :: s' /\ Pt m s') /\
                    (v =  0 -> exists s', s = CData (v,l) :: s' /\ Pf m s')))
       Q.
Proof.
  intros v l t f Pt Pf Q HTt HTf.
  eapply HT_decide_join' with (D := fun v => v = 0).
  apply ifNZ_spec_NZ.
  apply ifNZ_spec_Z.
  intros; omega.
  auto.
  auto.
Qed.

Lemma ifNZ_spec: forall v l t f Pt Pf Q,
  HT   t Pt Q ->
  HT   f Pf Q ->
  HT   (ifNZ t f)
       (fun m s => (exists s', s = CData (v,l) :: s' /\
                                   (v <> 0 -> Pt m s') /\
                                   (v =  0 -> Pf m s')))
       Q.
Proof.
  intros v l t f Pt Pf Q HTt HTf.
  eapply HT_strengthen_premise.
  eapply ifNZ_spec_helper; eauto.
  intros m s [s' [s_eq [HNZ HZ]]].
  destruct (dec_eq v 0); subst; intuition;
    eexists; intuition.
Qed.

(* I need to existentially bind [v] for the [ite_spec]. May have been
   easier to use existentials from the beginning ... *)
Lemma ifNZ_spec_existential: forall t f Pt Pf Q,
  HT   t Pt Q ->
  HT   f Pf Q ->
  HT   (ifNZ t f)
       (fun m s => (exists v l s', s = CData (v,l) :: s' /\
                                   (v <> 0 -> Pt m s') /\
                                   (v =  0 -> Pf m s')))
       Q.
Proof.
  intros t f Pt Pf Q HTt HTf.
  eapply HT_forall_exists.
  intro v.
  eapply HT_forall_exists.
  intro l.
  apply ifNZ_spec.
  auto.
  auto.
Qed.

(* Might make more sense to make [Qc] be the thing that [Qc] implies
   here.  I.e., this version has an implicit use of
   [HT_strengthen_premise] in it, which could always be inserted
   manually when needed. *)
Lemma ite_spec: forall c t f P Pt Pf Qc Q,
  HT   c P  Qc ->
  HT   t Pt Q ->
  HT   f Pf Q ->
  (forall m s, Qc m s -> (exists v l s', s = CData (v,l) :: s' /\
                                         (v <> 0 -> Pt m s') /\
                                         (v =  0 -> Pf m s')))
  ->
  HT   (ite c t f) P Q.
Proof.
  intros c t f P Pt Pf Qc Q HTc HTt HTf HQcP.
  unfold ite.
  eapply HT_compose.
  apply HTc.
  eapply HT_strengthen_premise.
  Focus 2.
  apply HQcP.
  apply ifNZ_spec_existential.
  auto.
  auto.
Qed.

(* A version of [ite_spec] that restricts the effect of the condition
   code [c] to pushing one value to the stack.

   In [genApplyRule_spec] we are considering a particular memory,
   [m0], so, here it helps to make the memory a parameter. *)
Lemma ite_spec_specialized: forall v c t f Q, forall m0 s0,
  let P := fun m s => m = m0 /\ s = s0 in
  HT c (fun m s => m = m0 /\ s = s0)
       (fun m s => m = m0 /\ s = (v,handlerTag) ::: s0) ->
  (v <> 0 -> HT t P Q) ->
  (v =  0 -> HT f P Q) ->
  HT (ite c t f) P Q.
Proof.
  introv HTc HZ HNZ.
  eapply ite_spec with (Pt := fun m s => v <> 0 /\ m = m0 /\ s = s0)
                       (Pf := fun m s => v =  0 /\ m = m0 /\ s = s0).
  eauto.
  eapply HT_fold_constant_premise; auto.
  eapply HT_fold_constant_premise; auto.

  introv Heq.
  simpl in Heq.
  jauto.
Qed.

Lemma cases_spec_base: forall d P Q,
  HT   d P Q -> HT   (cases nil d) P Q.
Proof.
  auto.
Qed.

Lemma cases_spec_step: forall c b cbs d P Qc Pt Pf Q,
  HT   c P Qc ->
  HT   b Pt Q ->
  HT   (cases cbs d) Pf Q ->
  (forall m s, Qc m s -> (exists v l s', s = CData (v,l) :: s' /\
                                         (v <> 0 -> Pt m s') /\
                                         (v =  0 -> Pf m s')))
  ->
  HT   (cases ((c,b)::cbs) d) P Q.
Proof.
  intros.
  eapply ite_spec; eauto.
Qed.

(* A specialized spec for the [cases] combinator.

   If

   - the conditions don't modify the existing stack or memory,
     but just push a value onto the stack, and that value is computed as
     a function of the stack and memory;

   - the different branches have different conclusions.

  Then if [cases] terminates, the conclusion of the first branch whose
  guard returned non-zero holds.

  Actually, that's what you get if you unfold this definition over a
  list of [(guard, branch)] pairs; this spec is just one step of
  unfolding. *)
Lemma cases_spec_step_specialized: forall c vc b cbs d P Qb Qcbs,
  (* This could be abstracted: code that transforms the stack by
  pushing one value computed from the existing stack and memory *)
  (forall m0 s0,
     HT   c (fun m s => P m0 s0 /\
                        m = m0 /\
                        s = s0)
            (fun m s => P m0 s0 /\
                        m = m0 /\ 
                        s = CData (vc m0 s0, handlerTag) :: s0)) ->
  HT   b P Qb ->
  HT   (cases cbs d) P Qcbs ->
  (forall m0 s0,
    HT   (cases ((c,b)::cbs) d) (fun m s => P m0 s0 /\
                                            m = m0 /\
                                            s = s0)
                                (fun m s => (vc m0 s0 <> 0 -> Qb m s) /\
                                            (vc m0 s0 = 0 -> Qcbs m s))).
Proof.
  intros c vc b cbs d P Qb Qcbs Hc Hb Hcbs.
  intros m0 s0.
  pose (Hc m0 s0) as Hcm0s0.
  eapply ite_spec with (Pt := (fun m s => P m s /\ vc m0 s0 <> 0))
                       (Pf := (fun m s => P m s /\ vc m0 s0 =  0)).
  exact Hcm0s0.

  apply (HT_consequence' _ _ _ _ _ Hb); intuition.
  elimtype False; jauto.

  apply (HT_consequence' _ _ _ _ _ Hcbs); intuition.
  elimtype False; jauto.

  intuition.
  exists (vc m0 s0).
  exists handlerTag.
  exists s0.
  intuition; subst; auto.
Qed.

(* XXX: move some of these defs up *)
Definition HProp := memory -> stack -> Prop.
(* [HProp] with ghost variables *)
Definition GProp := memory -> stack -> HProp.
(* Ghost prop Hoare triple *)
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

Definition HFun  := memory -> stack -> Z.

Lemma cases_spec_base_GT_specialized: forall cnil P Qnil,
  GT cnil P Qnil ->
  GT (cases [] cnil) P Qnil.
Proof.
unfold GT; intros; eapply cases_spec_base.
  eapply HT_strengthen_premise; eauto.
Qed.

Definition GT_push_v (c: code) (P: HProp) (v: HFun): Prop :=
  GT c P (fun m0 s0 m s => P m0 s0 /\
                           m = m0 /\
                           s = CData (v m0 s0, handlerTag) :: s0).
Definition GT_guard_v (b: code) (P: HProp) (v: HFun) (Q: GProp): Prop :=
  GT b (fun m s => P m s /\ v m s <> 0) Q.

Lemma cases_spec_step_GT_specialized: forall c v b cbs cnil P Qb Qcbs,
  GT_push_v c P v ->
  GT_guard_v b P v Qb ->
  GT (cases cbs cnil) P Qcbs ->
  GT (cases ((c,b)::cbs) cnil)
     P
     (fun m0 s0 m s => (v m0 s0 <> 0 -> Qb m0 s0 m s) /\
                       (v m0 s0 = 0 -> Qcbs m0 s0 m s)).
Proof.
  intros c vc b cbs d P Qb Qcbs Hc Hb Hcbs.
  intros m0 s0.
  pose (Hc m0 s0) as Hcm0s0.
  eapply ite_spec with (Pt := (fun m s => P m0 s0 /\ m = m0 /\ s = s0 /\ vc m0 s0 <> 0))
                       (Pf := (fun m s => P m0 s0 /\ m = m0 /\ s = s0 /\ vc m0 s0 =  0)).
  exact Hcm0s0.

  apply (HT_consequence' _ _ _ _ _ (Hb m0 s0)); intuition.
  elimtype False; jauto.

  fold cases.
  apply (HT_consequence' _ _ _ _ _ (Hcbs m0 s0)); intuition.
  elimtype False; jauto.

  intuition.
  exists (vc m0 s0).
  exists handlerTag.
  exists s0.
  intuition; subst; auto.
Qed.

Section IndexedCasesSpec.

Variable cnil: code.
Variable Qnil: GProp.
Variable I: Type.
Variable genC genB: I -> code.
Variable genQ: I -> GProp.
Variable genV: I -> HFun.

(* XXX: make these folds ? *)
Definition indexed_post: (list I) -> GProp :=
  fix f (indices: list I) :=
    fun m0 s0 m s =>
      match indices with
      | []            => Qnil m0 s0 m s
      | i :: indices' => (genV i m0 s0 <> 0 -> genQ i m0 s0 m s) /\
                         (genV i m0 s0 =  0 -> f indices' m0 s0 m s)
      end.

Variable P: HProp.
Definition indexed_hyps: (list I) -> Prop :=
  fix f (indices: list I) :=
    match indices with
    | []            => True
    | i :: indices' => GT_push_v (genC i) P (genV i) /\
                       GT_guard_v (genB i) P (genV i) (genQ i) /\
                       f indices'
    end.

Lemma indexed_cases_spec: forall is,
  GT cnil P Qnil ->
  indexed_hyps is ->
  GT (indexed_cases cnil genC genB is)
     P
     (indexed_post is).
Proof.
  induction is; intros.
  - eapply cases_spec_base_GT_specialized; eauto.
  - simpl in *.
    eapply cases_spec_step_GT_specialized; iauto.
Qed.

End IndexedCasesSpec.

(* NC: this might be a way to do "transformer" style ... *)
Lemma some_spec: forall c, forall m0 s0 s1,
  HT c 
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = s1) ->
  HT (some c)
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = (1,handlerTag) ::: s1).
Proof.
  introv HTc.
  unfold some.
  eapply HT_compose.
  eauto.
  eapply push_spec''.
Qed.

Definition none_spec     := push_spec''.
Definition genTrue_spec  := push_spec''.
Definition genFalse_spec := push_spec''.

Lemma genAnd_spec: forall b1 b2, forall m0 s0,
  HT genAnd
     (* We need [handlerTag] on [b2] because [genAnd] returns [b2] when
        [b1] is [true]. *)
     (fun m s => m = m0 /\ s = CData (boolToZ b1,handlerTag) ::
                               CData (boolToZ b2,handlerTag) :: s0)
     (fun m s => m = m0 /\ s = CData (boolToZ (andb b1 b2),handlerTag) :: s0).
Proof.
  intros.
  unfold genAnd.
  destruct b1; eapply HT_strengthen_premise.
    eapply ifNZ_spec_NZ with (v:=1).
    apply nop_spec.
    omega.
    simpl; jauto.

    eapply ifNZ_spec_Z with (v:=0).
    eapply HT_compose.
    eapply pop_spec.
    eapply genFalse_spec.
    reflexivity.
    simpl; jauto.
Qed.

Lemma genOr_spec: forall b1 b2, forall m0 s0,
  HT genOr
     (fun m s => m = m0 /\ s = CData (boolToZ b1,handlerTag) ::
                               CData (boolToZ b2,handlerTag) :: s0)
     (fun m s => m = m0 /\ s = CData (boolToZ (orb b1 b2),handlerTag) :: s0).
Proof.
  intros.
  unfold genOr.
  destruct b1; eapply HT_strengthen_premise.

    eapply ifNZ_spec_NZ with (v:=1).
    eapply HT_compose.
    eapply pop_spec.
    eapply genTrue_spec.
    omega.
    simpl; jauto.

    eapply ifNZ_spec_Z with (v:=0).
    apply nop_spec.
    reflexivity.
    simpl; jauto.
Qed.

Lemma genNot_spec_general: forall v, forall m0 s0,
  HT genNot
     (fun m s => m = m0 /\ s = CData (v, handlerTag) :: s0)
     (fun m s => m = m0 /\ 
                 s = CData (boolToZ (v =? 0),handlerTag) :: s0).
Proof.
  intros.
  unfold genNot.
  cases (v =? 0) as Heq.
  - apply Z.eqb_eq in Heq.
    eapply HT_strengthen_premise.
    + eapply ifNZ_spec_Z.
      * eapply genTrue_spec.
      * eauto.
    + jauto.
  - apply Z.eqb_neq in Heq.
    eapply HT_strengthen_premise.
    + eapply ifNZ_spec_NZ.
      * eapply genFalse_spec.
      * eauto.
    + jauto.
Qed.

Lemma genNot_spec: forall b, forall m0 s0,
  HT genNot
     (fun m s => m = m0 /\ s = (boolToZ b, handlerTag) ::: s0)
     (fun m s => m = m0 /\ s = (boolToZ (negb b), handlerTag) ::: s0).
Proof.
  intros.
  eapply HT_weaken_conclusion.
  - eapply genNot_spec_general.
  - cases b; auto.
Qed.

Lemma genImpl_spec: forall b1 b2, forall m0 s0,
  HT genImpl
     (fun m s => m = m0 /\ s = CData (boolToZ b1,handlerTag) ::
                               CData (boolToZ b2,handlerTag) :: s0)
     (fun m s => m = m0 /\ s = CData (boolToZ (implb b1 b2),handlerTag) :: s0).
Proof.
  intros.
  eapply HT_weaken_conclusion.
  unfold genImpl.
  eapply HT_compose.
  eapply genNot_spec.
  eapply genOr_spec.
  simpl. cases b1; cases b2; iauto.
Qed.

(* NC: use [Z.eqb_eq] and [Z.eqb_neq] to relate the boolean equality
   to propositional equality. *)
Lemma genTestEqual_spec: forall c1 c2, forall v1 v2, forall m0,
  (forall s0,
     HT c1
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (v1,handlerTag) ::: s0)) ->
  (forall s0,
     HT c2
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (v2,handlerTag) ::: s0)) ->
  (forall s0,
     HT (genTestEqual c1 c2)
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (boolToZ (v1 =? v2),handlerTag) ::: s0)).
Proof.
  intros.
  unfold genTestEqual.
  eapply HT_compose; eauto.
  eapply HT_compose; eauto.
  eapply HT_compose.
  eapply sub_spec.
  eapply HT_weaken_conclusion.
  eapply genNot_spec_general.

  (*
  Z.eqb_eq: forall n m : Z, (n =? m) = true <-> n = m
  Z.eqb_neq: forall x y : Z, (x =? y) = false <-> x <> y
  *)
  Lemma basic_arithmetic:
    forall v1 v2, (v2 - v1 =? 0) = (v1 =? v2).
  Proof.
    intuition; cases (v1 =? v2);
    try (rewrite Z.eqb_eq in *); try (rewrite Z.eqb_neq in *); omega.
  Qed.

  rewrite basic_arithmetic in *; intuition.
Qed.

(* NC: [valid_address a m0] implies [upd_m] succeeds *)
Conjecture storeAt_spec_wp: forall a vl Q,
  forall m s,
  HT (storeAt a)
     (fun m0 s0 => s0 = vl ::: s /\
                   upd_m a vl m0 = Some m /\
                   Q m s)
     Q.

Lemma HT_compose_bwd:
  forall (c1 c2 : code) (P Q R : memory -> stack -> Prop),
    HT c2 Q R -> HT c1 P Q -> HT (c1 ++ c2) P R.
Proof.
  intros; eapply HT_compose; eauto.
Qed.

Lemma valid_address_upd: forall a a' vl m m',
  valid_address a m ->
  upd_m a' vl m = Some m' ->
  valid_address a m'.
Proof.
  unfold valid_address; intuition.
  unfold upd_m in *.
  destruct (a' <? 0).
  - false.
  - erewrite update_preserves_length; eauto.
Qed.

Lemma store_twice_test: forall a1 a2 vl1 vl2,
  a1 <> a2 ->
  forall m s,
  valid_address a1 m ->
  valid_address a2 m ->
  HT (storeAt a1 ++ storeAt a2)
     (fun m0 s0 => m0 = m /\
                   s0 = CData vl1 :: CData vl2 :: s)
     (fun m1 s1 => s1 = s /\
                   exists m', upd_m a1 vl1 m = Some m' /\
                              upd_m a2 vl2 m' = Some m1).
Proof.
  introv Hneq Hvalid1 Hvalid2; intros.

  eapply valid_store in Hvalid1.
  destruct Hvalid1 as [m' ?]; eauto.

  eapply valid_address_upd with (m':=m') in Hvalid2.
  eapply valid_store in Hvalid2.
  destruct Hvalid2; eauto.

  eapply HT_compose_bwd.
  apply storeAt_spec_wp.
  eapply HT_strengthen_premise.
  apply storeAt_spec_wp.

  intuition; subst; eauto.
  eauto.
Qed.

(* Follow from a more general [push'_spec_wp]. *)
Lemma genTrue_spec_wp: forall Q,
  HT genTrue
     (fun m s => Q m ((1,handlerTag):::s))
     Q.
Proof.
  eapply push_spec.
Qed.

Lemma genFalse_spec_wp: forall Q,
  HT genFalse
     (fun m s => Q m ((0,handlerTag):::s))
     Q.
Proof.
  eapply push_spec.
Qed.

Lemma nop_spec_wp: forall Q,
  HT nop Q Q.
Proof.
  unfold nop, HT; simpl; intros.
  eexists; eexists; intuition eauto.
  apply_f_equal runsToEndDone; rec_f_equal ltac:(try omega; eauto).
Qed.

Lemma ret_specEscape: forall raddr (P: memory -> stack -> Prop),
  HTEscape raddr [Ret]
    (fun m s => exists s', s = (CRet raddr false false::s') /\ P m s')
    (fun m s => (P m s , Success)).
Proof.
  intros. cases raddr; subst.
  unfold HTEscape. intros. intuition.
  jauto_set_hyps; intuition.
  repeat eexists.
  eauto.

  (* Load an instruction *)
  subst.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_success; auto.
  eapply star_step.
  eapply cstep_ret_p; auto.
  eapply cptr_done.
  eapply star_refl.
  auto.
Qed.

Lemma jump_specEscape_Failure: forall raddr (P: memory -> stack -> Prop),
  HTEscape raddr [Jump]
           (fun m s => exists s0, (-1, handlerTag) ::: s0 = s /\ P m s0)
           (fun m s => (P m s , Failure)).
Proof.
  intros.
  unfold HTEscape. intros.
  jauto_set_hyps; intuition.
  repeat eexists.
  eauto.

  (* Load an instruction *)
  subst.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_fail; auto.
  eapply star_step.
  eapply cstep_jump_p; auto.
  eapply star_refl.
  auto.
  simpl; eauto; omega.
Qed.

Lemma skipNZ_specEscape: forall r c1 c2 v P1 P2 Q,
  (v =  0 -> HTEscape r c1 P1 Q) ->
  (v <> 0 -> HTEscape r c2 P2 Q) ->
  HTEscape r ((skipNZ (length c1) ++ c1) ++ c2)
           (fun m s => exists s0, s = (v, handlerTag) ::: s0 /\
                                  (v =  0 -> P1 m s0) /\
                                  (v <> 0 -> P2 m s0))
           Q.
Proof.
  intros.
  unfold skipNZ.
  destruct (dec_eq v 0); subst.
  - eapply HTEscape_append.
    eapply HTEscape_compose.
    eapply skipNZ_spec_Z; auto.
    eapply HTEscape_strengthen_premise; iauto.
  - eapply HTEscape_compose.
    eapply skipNZ_continuation_spec_NZ; auto.
    eapply HTEscape_strengthen_premise; iauto.
Qed.

Lemma ifNZ_specEscape: forall r t f v Pt Pf Q,
  (v <> 0 -> HTEscape r t Pt Q) ->
  (v =  0 -> HTEscape r f Pf Q) ->
  HTEscape r (ifNZ t f)
           (fun m s => exists s0, s = (v, handlerTag) ::: s0 /\
                                  (v <> 0 -> Pt m s0) /\
                                  (v =  0 -> Pf m s0))
           Q.
Proof.
  intros.
  unfold ifNZ.
  rewrite <- app_ass.
  eapply HTEscape_strengthen_premise.
  eapply skipNZ_specEscape with (v:=v).
  - intros.
    eapply HTEscape_append; eauto.
  - intros.
    eauto.
  - jauto.
Qed.

End CodeSpecs.
