Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import LibTactics.
Import ListNotations. 

Require Import TMUInstr.
Require Import Lattices.
Require Import Concrete.
Require Import Rules. 
Require Import CodeGen.
Require Import CLattices.
Require Import ConcreteMachine.
Require Import Concrete. (* [update_cache_spec_rvec] *)
Require Import Coq.Arith.Compare_dec.

Section TMUSpecs.
Local Open Scope Z_scope.


Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}.

Definition imemory : Type := list (@Instr T).
Definition memory : Type := list (@Atom T). 
Definition stack : Type := list (@CStkElmt T). 
Definition code := list (@Instr T).
Definition state := @CS T.

Section Glue.

Import Vector.VectorNotations.

Local Open Scope nat_scope.

(* Old definition; replaced below. 
Definition glue {n:nat} (vls :Vector.t T n) : (option T * option T * option T) :=
match vls with
| [] => (None,None,None)
| [t1] => (Some t1, None,None)
| [t1; t2] => (Some t1, Some t2, None)
| (t1::(t2::(t3::_))) => (Some t1, Some t2, Some t3)
end. 
*)

Definition nth_order_option {n:nat} (vls: Vector.t T n) (m:nat): option T :=
  match le_lt_dec n m with
  | left _ => None
  | right p => Some (Vector.nth_order vls p)
  end.

Lemma of_nat_lt_proof_irrel:
  forall (m n: nat) (p q: m < n),
    Fin.of_nat_lt p = Fin.of_nat_lt q.
Proof.
  induction m; intros.
    destruct n.
      false; omega.
      reflexivity.
    destruct n.
      false; omega.
      simpl; erewrite IHm; eauto.
Qed.

(* NC: this took a few tries ... *)
Lemma nth_order_proof_irrel:
  forall (m n: nat) (v: Vector.t T n) (p q: m < n),
    Vector.nth_order v p = Vector.nth_order v q.
Proof.
  intros.
  unfold Vector.nth_order.
  erewrite of_nat_lt_proof_irrel; eauto.
Qed.

Lemma nth_order_option_Some: forall (n:nat) (vls: Vector.t T n) m,
  forall (lt: m < n),
  nth_order_option vls m = Some (Vector.nth_order vls lt).
Proof.
  intros.
  unfold nth_order_option.
  destruct (le_lt_dec n m).
  false; omega.
  (* NC: Interesting: here we have two different proofs [m < n0] being
  used as arguments to [nth_order], and we need to know that the
  result of [nth_order] is the same in both cases.  I.e., we need
  proof irrelevance! *)
  erewrite nth_order_proof_irrel; eauto.
Qed.

Definition glue {n:nat} (vls :Vector.t T n) : (option T * option T * option T) :=
(nth_order_option vls 0, nth_order_option vls 1, nth_order_option vls 2).

End Glue.

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
Inductive runsToEnd (Rstep: CS -> CS -> Prop) : Z -> Z -> @CS T -> @CS T -> Prop :=
| runsToEndDone : forall n cs,
  fst (pc cs) = n -> 
  runsToEnd Rstep n n cs cs
  (* NC: do we need to worry about [n <= n' <= n'']? *)
| runsToEndStep: forall n n' n'' cs cs' cs'',
  fst (pc cs) = n ->
  Rstep cs cs' ->
  fst (pc cs') = n' ->
  (* DD: I just comment out these for now, as the new hyp breaks composition lemma below *)
  (* n <> n'' -> *)  (* OR:  n < n'' -> *) (* BEFORE: n < n' -> *) 
  runsToEnd Rstep n' n'' cs' cs'' -> 
  runsToEnd Rstep n  n'' cs  cs''.

(* APT: With second option above ( n < n'') it is
   easy enough to prove the following two lemmas.
   But at the moment, Nathan and I don't see any
   strong reason to include this restriction...

Lemma runsToEnd_bounded: forall step pc0 pc1 s0 s1, 
  runsToEnd step pc0 pc1 s0 s1 -> pc0 <= pc1. 
Proof.
  intros.  inv H. 
  omega.
omega.
Qed.

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
  apply runsToEnd_bounded in H4. 
  omega.
Qed.
*)

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
  runsToEnd cstep_p n n' 
             (CState cache0 mem fh imem stk0 (n, handlerLabel) true)
             (CState cache1 mem fh imem stk1 (n', handlerLabel) true).

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

(* ================================================================ *)
(* Specs for concrete code *)

(* Simplest example: the specification of a single instruction run in
privileged mode *)
Lemma add_spec: forall (z1 z2: Z) (l1 l2: T) (m: memory) (s: stack),
  HT  [Add]
      (fun m1 s1 => m1 = m /\ s1 = CData (z1,l1) :: CData (z2,l2) :: s)
      (fun m2 s2 => m2 = m /\ s2 = CData (z1 + z2, handlerLabel) :: s).
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
  eapply runsToEndStep; auto.
  eapply cp_add ; eauto.
  
  (* Finish running *)
  eapply runsToEndDone; auto.
Qed.

Lemma add_sub_spec: forall (z1 z2: Z) (l1 l2: T) (m: memory) (s: stack),
  HT   (Add :: Sub :: nil)
      (fun m1 s1 => m1 = m /\ s1 = CData (z1,l1) :: CData (z2,l2) :: CData (z2,l2) :: s)
      (fun m2 s2 => m2 = m /\ s2 = CData (z1, handlerLabel) :: s).
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
  eapply runsToEndStep; auto.
  eapply cp_add; eauto.
  
  (* Run an instruction *)
  eapply runsToEndStep; auto.
  eapply cp_sub; eauto.

  (* Finish running *)
  let t := (auto || simpl; omega) in
  apply_f_equal @runsToEndDone; rec_f_equal t.
Qed.

Lemma sub_spec: forall z1 l1 z2 l2, forall m0 s0,
  HT [Sub]
     (fun m s => m = m0 /\ s = (z1,l1) ::: (z2,l2) ::: s0)
     (fun m s => m = m0 /\ s = (z1 - z2,handlerLabel) ::: s0).
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
  eapply runsToEndStep; auto.
  eapply cp_sub; eauto.
  simpl.
  constructor; auto.
Qed.

Lemma push_spec: forall v P,
  HT   (push v :: nil)
       (fun m s => P m (CData (v,handlerLabel) :: s))
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
  eapply runsToEndStep; auto.
  eapply cp_push ; eauto.
  simpl.
  constructor; auto.
Qed.

Lemma push_spec': forall v P,
  HT   (push v :: nil)
       P
       (fun m s => head s = Some (CData (v,handlerLabel)) /\
                            P m (tail s)).
Proof.
  intros v P.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP Hn'.
  exists (CData (v, handlerLabel) :: stk0). eexists c0.
  intuition.
  
  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. intuition. 

  (* Run an instruction *)
  eapply runsToEndStep; auto.
  eapply cp_push ; eauto.
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
     (fun m s => m = m0 /\ s = CData (v,handlerLabel) :: s0).
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
  eapply runsToEndStep; auto.
  eapply cp_push; eauto.
  simpl.
  constructor; auto.
Qed.

Lemma load_spec: forall a al v vl, forall m0 s0,
  index_list_Z a m0 = Some (v,vl) ->
  HT [Load]
     (fun m s => m = m0 /\ s = CData (a,al) :: s0)
     (fun m s => m = m0 /\ s = CData (v,handlerLabel) :: s0).
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
  eapply runsToEndStep; auto.
  eapply cp_load; eauto.
  simpl.
  constructor; auto.
Qed.

Lemma loadFrom_spec: forall a v vl, forall m0 s0,
  index_list_Z a m0 = Some (v,vl) ->
  HT (loadFrom a)
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = CData (v,handlerLabel) :: s0).
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
  eapply runsToEndStep; auto.
  eapply cp_branchnz; eauto.
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

Lemma update_list_Some (T': Type): forall (v: T') l a,
  a < length l ->
  exists l', update_list a v l = Some l'.
Proof.
  Admitted.

(* This is the other half of the [update_list_spec] in Utils.v ...
   except that I use [upd_m] and [read_m] instead. *)

Lemma update_list_spec' (X: Type): forall (x: X) l a a' l',
  a <> a' ->
  upd_m a' x l = Some l' ->
  read_m a l = read_m a l'.
Proof.
  Admitted.

End MoveThisToUtils.

(* NC: to prove that addresses are valid per this definition, we just
   need to know that that the memory is at least as large as the
   [tmuCacheSize] defined in Concrete.v, since we only use
   [valid_address] assumptions for [addrTag*]. *)
Definition valid_address a (m: memory) :=
  (0 <= a) /\ (Z.to_nat a < length m)%nat.

Lemma valid_store: forall a v m,
  valid_address a m ->
  exists m', upd_m a v m = Some m'.
Proof.
  intros.
  unfold valid_address in *.
  unfold upd_m.
  assert (a <? 0 = false) as Heq.
  { unfold "<?", "?=".
    induction a; simpl; try reflexivity.
    false; zify; omega. }
  rewrite Heq.
  eapply update_list_Some.
  intuition.
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
  eapply runsToEndStep; auto.
  eapply cp_store; eauto.

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
  eapply runsToEndStep; eauto. 
  eapply cp_branchnz ; eauto. 

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
  eapply runsToEndStep; auto.
  eapply cp_branchnz ; eauto. 
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
       (fun m s => m = m0 /\ s = (v,handlerLabel) ::: s0) ->
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
                        s = CData (vc m0 s0, handlerLabel) :: s0)) ->
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
  exists handlerLabel.
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
                           s = CData (v m0 s0, handlerLabel) :: s0).
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
  exists handlerLabel.
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
     (fun m s => m = m0 /\ s = (1,handlerLabel) ::: s1).
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
     (* We need [handlerLabel] on [b2] because [genAnd] returns [b2] when
        [b1] is [true]. *)
     (fun m s => m = m0 /\ s = CData (boolToZ b1,handlerLabel) ::
                               CData (boolToZ b2,handlerLabel) :: s0)
     (fun m s => m = m0 /\ s = CData (boolToZ (andb b1 b2),handlerLabel) :: s0).
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
     (fun m s => m = m0 /\ s = CData (boolToZ b1,handlerLabel) ::
                               CData (boolToZ b2,handlerLabel) :: s0)
     (fun m s => m = m0 /\ s = CData (boolToZ (orb b1 b2),handlerLabel) :: s0).
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
     (fun m s => m = m0 /\ s = CData (v, handlerLabel) :: s0)
     (fun m s => m = m0 /\ 
                 s = CData (boolToZ (v =? 0),handlerLabel) :: s0).
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
     (fun m s => m = m0 /\ s = (boolToZ b, handlerLabel) ::: s0)
     (fun m s => m = m0 /\ s = (boolToZ (negb b), handlerLabel) ::: s0).
Proof.
  intros.
  eapply HT_weaken_conclusion.
  - eapply genNot_spec_general.
  - cases b; auto.
Qed.

(* NC: use [Z.eqb_eq] and [Z.eqb_neq] to relate the boolean equality
   to propositional equality. *)
Lemma genTestEqual_spec: forall c1 c2, forall v1 v2, forall m0,
  (forall s0,
     HT c1
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (v1,handlerLabel) ::: s0)) ->
  (forall s0,
     HT c2
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (v2,handlerLabel) ::: s0)) ->
  (forall s0,
     HT (genTestEqual c1 c2)
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (boolToZ (v1 =? v2),handlerLabel) ::: s0)).
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

(* ================================================================ *)
(* Fault-handler-specific specs *)

(* XXX: NC: Copied from ../mach_exec/TMUFaultRoutine.v. I'm not sure
how that file relates to ./FaultRoutine.v *)
Definition handler_initial_mem_matches 
           (opcode: OpCode)
           (op1lab: option T) (op2lab:option T) (op3lab:option T) (pclab: T) 
           (m: memory) : Prop := 
  index_list_Z addrOpLabel m = Some(opCodeToZ opcode,handlerLabel)
  /\ (match op1lab with
      | Some op1 => index_list_Z addrTag1 m = Some (labToZ op1,handlerLabel)
      |    None=> True
   end)  
  /\ (match op2lab with
      | Some op2 => index_list_Z addrTag2 m = Some (labToZ op2,handlerLabel)
      | None => True
      end)
  /\ (match op3lab with
      | Some op3 => index_list_Z addrTag3 m = Some (labToZ op3,handlerLabel)
      | None => True
      end)
  /\ index_list_Z addrTagPC m = Some (labToZ pclab,handlerLabel)
.

(* APT: Just a little sanity check that these definitions are somewhat coherent. *)
Lemma init_init: forall m op t1 t2 t3 tpc, @cache_hit T CLatt m (opCodeToZ op,labToZ t1,labToZ t2,labToZ t3,labToZ tpc) ->
handler_initial_mem_matches op (Some t1) (Some t2) (Some t3) tpc m.
Proof.
  intros.
  inv H. inv OP. inv TAG1. inv TAG2. inv TAG3. inv TAGPC. 
  econstructor; eauto.
Qed.

(* Connecting to the definition used in FaultRoutine.v : *)
Lemma init_enough: forall {n} (vls:Vector.t T n) m opcode pcl,
    let '(op1l,op2l,op3l) := glue vls in
    cache_hit m (mvector opcode op1l op2l op3l pcl) ->
    handler_initial_mem_matches 
      opcode
      (nth_order_option vls 0)
      (nth_order_option vls 1)
      (nth_order_option vls 2)
      pcl m.
Proof.
  intros. unfold glue. intro. 
  destruct (nth_order_option vls 0); destruct (nth_order_option vls 1);
    destruct (nth_order_option vls 2); unfold mvector in H; apply init_init in H;
    auto; unfold handler_initial_mem_matches in *; intuition. 
Qed.

Variable fetch_rule_impl: fetch_rule_impl_type.
Variable (opcode: OpCode).
Definition n := projT1 (fetch_rule_impl opcode).
Definition am := projT2 (fetch_rule_impl opcode).
Variable (vls: Vector.t T n).
Variable (pcl: T).
Variable (m0: memory).

Hypothesis initial_mem_matches:
  handler_initial_mem_matches
    opcode
    (nth_order_option vls 0)
    (nth_order_option vls 1)
    (nth_order_option vls 2)
    pcl m0.

Definition eval_var := mk_eval_var vls pcl.

Lemma genVar_spec:
  forall v l,
    eval_var v = l ->
    forall s0,
      HT   (genVar v)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (labToZ l, handlerLabel) :: s0).
Proof.
  intros v l Heval_var s0.
  destruct v; simpl; eapply loadFrom_spec;
  simpl in *; unfold handler_initial_mem_matches in *.

  (* Most of the cases are very similar ... *)
  Ltac nth_order_case k :=
    erewrite (nth_order_option_Some n vls k) in *;
    intuition;
    subst; auto;
    eauto.
  nth_order_case 0%nat.
  nth_order_case 1%nat.
  nth_order_case 2%nat.

  intuition.
  subst; auto.
  eauto.
Qed.

Hypothesis genJoin_spec: forall l l' m0 s0,
  HT   genJoin
       (fun m s => m = m0 /\
                   s = CData (labToZ l, handlerLabel) ::
                       CData (labToZ l', handlerLabel) :: s0)
       (fun m s => m = m0 /\
                   s = CData (labToZ (join l l'), handlerLabel) :: s0).

Lemma genExpr_spec: forall (e: rule_expr n),
  forall l,
    eval_expr eval_var e = l ->
    forall s0,
      HT   (genExpr e)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (labToZ l, handlerLabel) :: s0).
Proof.
  induction e; intros ? Heval_expr ?;
    simpl; simpl in Heval_expr.
  eapply genVar_spec; eauto.
  eapply HT_compose.
  eapply IHe2; eauto.
  eapply HT_compose.
  eapply IHe1; eauto.
  rewrite <- Heval_expr.
  eapply genJoin_spec.
Qed.

(* XXX: we can discharge this by implementing [genFlows] in terms of
   [genJoin], and using the fact that [flows l l' = true <-> join l l' = l']. *)
Hypothesis genFlows_spec: forall l l' m0 s0,
  HT   genFlows
       (fun m s => m = m0 /\
                   s = CData (labToZ l, handlerLabel) ::
                       CData (labToZ l', handlerLabel) :: s0)
       (fun m s => m = m0 /\
                   s = CData (boolToZ (flows l l'), handlerLabel) :: s0).

Lemma genScond_spec: forall (c: rule_scond n),
  forall b,
    eval_cond eval_var c = b ->
    forall s0,
      HT   (genScond c)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (boolToZ b, handlerLabel) :: s0).
Proof.
  induction c; intros; simpl;
    try (simpl in H); subst.

  (* True *)
  eapply push_spec''.

  (* Flows *)
  eapply HT_compose.
  eapply genExpr_spec.
  eauto.
  eapply HT_compose.
  eapply genExpr_spec.
  eauto.
  eapply genFlows_spec.

  (* And *)
  eapply HT_compose.
  eapply IHc2.
  eauto.
  eapply HT_compose.
  eapply IHc1.
  eauto.
  eapply genAnd_spec.

  (* Or *)
  eapply HT_compose.
  eapply IHc2.
  eauto.
  eapply HT_compose.
  eapply IHc1.
  eauto.
  eapply genOr_spec.
Qed.

(* XXX: how to best model [option]s and monadic sequencing in the code
   gens?  E.g., for [genApplyRule_spec], I need to handle both [Some
   (Some l1, l2)] and [Some (None, l2)].  Do I do different things to
   memory in these cases? If so I need to distinguish these cases in
   my stack returns.

   Also, modeling [option]s in the generated code might make the
   correctness proof easier? *)

(* NC: Nota bene: we should only need to reason about what
   [genApplyRule] does for the current opcode, since that's the only
   code that is going to run. *)

(* XXX: could factor out all the [apply_rule] assumptions
   below as:

     Parameter ar.
     Hypothesis apply_rule_eq: apply_rule am vls pcl = ar.

   and then use [ar] in place of [apply_rule am vls pcl] everywhere.
*)

Lemma genApplyRule_spec_Some_Some:
  forall l1 l2,
    apply_rule am vls pcl = Some (Some l1, l2) ->
    forall s0,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (        1, handlerLabel) :: (* [Some (...)] *)
                           CData (        1, handlerLabel) :: (* [Some l1] *)
                           CData (labToZ l1, handlerLabel) ::
                           CData (labToZ l2, handlerLabel) :: s0).
Proof.
  introv Happly. intros.
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.
  cases (labRes am); try (solve [false; auto]).
  inversion Happly; subst.

  eapply ite_spec_specialized with (v:=boolToZ true).
    eapply genScond_spec; auto.

    intros.
    eapply HT_compose.

      apply genExpr_spec.
      eauto.

      eapply some_spec.
      eapply some_spec.
      eapply genExpr_spec.
      eauto.

    intros; false; omega.
Qed.

Lemma genApplyRule_spec_Some_None:
  forall l2,
    apply_rule am vls pcl = Some (None, l2) ->
    forall s0,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (        1, handlerLabel) :: (* [Some (...)] *)
                           CData (        0, handlerLabel) :: (* [None] *)
                           CData (labToZ l2, handlerLabel) :: s0).
Proof.
  introv Happly. intros.
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.
  cases (labRes am); try (solve [false; auto]).
  inversion Happly; subst.

  eapply ite_spec_specialized with (v:=boolToZ true).
    eapply genScond_spec; auto.

    intros.
    eapply HT_compose.

      apply genExpr_spec.
      eauto.

      eapply some_spec.
      eapply none_spec.

    intros; false; omega.
Qed.

Lemma genApplyRule_spec_None:
    apply_rule am vls pcl = None ->
    forall s0,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = CData (0, handlerLabel) :: s0). (* [None] *)
Proof.
  introv Happly. intros.
  unfold genApplyRule.
  unfold apply_rule in Happly.
  cases_if in Happly.

  eapply ite_spec_specialized with (v:=boolToZ false); intros.
    eapply genScond_spec; auto.

    unfold boolToZ in *; false; omega.

    apply none_spec.
Qed.

Definition listify_apply_rule
  (ar: option (option T * T)) (s0: stack): stack
:=
  match ar with
  | None                => CData (0, handlerLabel) :: s0
  | Some (None,    lpc) => CData (1, handlerLabel) ::
                           CData (0, handlerLabel) ::
                           CData (labToZ lpc, handlerLabel) :: s0
  | Some (Some lr, lpc) => CData (1, handlerLabel) ::
                           CData (1, handlerLabel) ::
                           CData (labToZ lr, handlerLabel) ::
                           CData (labToZ lpc, handlerLabel) :: s0
  end.

Lemma genApplyRule_spec:
  forall ar,
    apply_rule am vls pcl = ar ->
    forall s0,
      HT   (genApplyRule am)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = listify_apply_rule ar s0).
Proof.
  intros.
  case_eq ar; intros p ?; subst.
  - destruct p as [o l2]; case_eq o; intros l1 ?; subst.
    + eapply genApplyRule_spec_Some_Some; eauto.
    + eapply genApplyRule_spec_Some_None; eauto.
  - eapply genApplyRule_spec_None; eauto.
Qed.

Lemma genApplyRule_spec_GT:
  forall ar,
    apply_rule am vls pcl = ar ->
      GT (genApplyRule am)
         (fun m s => m = m0)
         (fun m0' s0 m s => m = m0 /\
                            s = listify_apply_rule ar s0).
Proof.
  unfold GT; intros.
  eapply HT_consequence; eauto.
  - eapply genApplyRule_spec; eauto.
  - simpl; intuition (subst; eauto).
  - simpl; intuition (subst; eauto).
Qed.

Lemma genCheckOp_spec:
  forall opcode', forall s0,
    HT (genCheckOp opcode')
      (fun m s => m = m0 /\
                  s = s0)
      (fun m s => m = m0 /\
                  s = (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode)
                      ,handlerLabel) ::: s0).
Proof.
  intros.
  unfold genCheckOp.
  eapply genTestEqual_spec.
  eapply push_spec''.
  intros.
  eapply loadFrom_spec.
  unfold handler_initial_mem_matches in *.
  iauto.
Qed.

Lemma genCheckOp_spec_GT:
  forall opcode',
    GT (genCheckOp opcode')
       (fun m s => m = m0)
       (fun m0' s0 m s => m = m0 /\
                          s = (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode)
                               ,handlerLabel) ::: s0).
Proof.
  unfold GT; intros.
  eapply HT_consequence; eauto.
  - eapply genCheckOp_spec; eauto.
  - simpl; intuition (subst; eauto).
  - simpl; intuition (subst; eauto).
Qed.

Section FaultHandlerSpec.

Variable ar: option (option T * T).
Hypothesis H_apply_rule: apply_rule am vls pcl = ar.

(* Don't really need to specify [Qnil] since it will never run *)
Definition Qnil: GProp := fun m0' s0 m s => True.
Definition genV: OpCode -> HFun :=
  fun i _ _ => boolToZ (opCodeToZ i =? opCodeToZ opcode).
Definition genC: OpCode -> code := genCheckOp.
Definition genB: OpCode -> code := genApplyRule' fetch_rule_impl.
Definition genQ: OpCode -> GProp :=
         (fun i m0' s0 m s => m = m0 /\
                              s = listify_apply_rule ar s0).

Lemma genCheckOp_spec_GT_push_v:
  forall opcode',
    GT_push_v (genC opcode')
              (fun m s => m = m0)
              (genV opcode').
Proof.
  intros; eapply GT_consequence'.
  eapply genCheckOp_spec_GT.
  eauto.
  intuition (subst; intuition).
Qed.

Lemma dec_eq_OpCode: forall (o o': OpCode),
  o = o' \/ o <> o'.
Proof.
  destruct o; destruct o'; solve [ left; reflexivity | right; congruence ].
Qed.

Lemma labToZ_inj: forall opcode opcode',
  (boolToZ (opCodeToZ opcode' =? opCodeToZ opcode) <> 0) ->
  opcode' = opcode.
Proof.
  intros o o'.
  destruct o; destruct o'; simpl; solve [ auto | intros; false; omega ].
Qed.

Lemma genApplyRule'_spec_GT_guard_v:
  forall opcode',
    GT_guard_v (genB opcode')
               (fun m s => m = m0)
               (genV opcode')
               (genQ opcode').
Proof.
  (* NC: This proof is ugly ... not sure where I've gone wrong, but I
  have ... *)
  intros.
  cases (dec_eq_OpCode opcode' opcode) as Eq; clear Eq.
  - eapply GT_consequence'.
    + unfold genB, genApplyRule'.
      subst opcode'.
      fold am.
      eapply genApplyRule_spec_GT; eauto.
    + iauto.
    + iauto.
  - unfold GT_guard_v, GT, HT.
    intros.
    unfold genV in *.
    pose (labToZ_inj opcode opcode').
    false; intuition.
Qed.

Lemma H_indexed_hyps: indexed_hyps _ genC genB genQ genV (fun m s => m = m0) opcodes.
Proof.
  simpl.
  intuition; solve
    [ eapply genCheckOp_spec_GT_push_v
    | eapply genApplyRule'_spec_GT_guard_v ].
Qed.

Lemma genFaultHandlerStack_spec_GT:
  GT (genFaultHandlerStack fetch_rule_impl)
     (fun m s => m = m0)
     (fun m0' s0 m s => m = m0 /\
                        s = listify_apply_rule ar s0).
Proof.
  intros.
  eapply GT_consequence'.
  unfold genFaultHandlerStack.
  eapply indexed_cases_spec with (Qnil:=Qnil).
  - Case "default case that we never reach".
    unfold GT; intros.
    eapply HT_consequence.
    eapply nop_spec.
    iauto.
    unfold Qnil; iauto.
  - exact H_indexed_hyps.
  - iauto.
  - Case "untangle post condition".
    simpl.
    assert (0 = 0) by reflexivity.
    assert (1 <> 0) by omega.
    (* NC: Otherwise [cases] fails.  Thankfully, [cases] tells us this
    is the problematic lemma, whereas [destruct] just spits out a huge
    term and says it's ill typed *)
    clear H_apply_rule.
    cases opcode;
      unfold genV, genQ; subst; simpl; intuition.
Qed.

(* Under our assumptions, [genFaultHandlerStack] just runs the appropriate
   [genApplyRule]: *)
Lemma genFaultHandlerStack_spec:
    forall s0,
      HT   (genFaultHandlerStack fetch_rule_impl)
           (fun m s => m = m0 /\
                       s = s0)
           (fun m s => m = m0 /\
                       s = listify_apply_rule ar s0).
Proof.
  intros.
  eapply HT_consequence'.
  eapply genFaultHandlerStack_spec_GT.
  iauto.
  simpl; iauto.
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

Conjecture valid_address_upd: forall a a' vl m m',
  valid_address a m ->
  upd_m a' vl m = Some m' ->
  valid_address a m'.

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
Conjecture genTrue_spec_wp: forall Q,
  HT genTrue
     (fun m s => Q m ((1,handlerLabel):::s))
     Q.

Conjecture genFalse_spec_wp: forall Q,
  HT genFalse
     (fun m s => Q m ((0,handlerLabel):::s))
     Q.

Lemma nop_spec_wp: forall Q,
  HT nop Q Q.
Proof.
  unfold nop, HT; simpl; intros.
  eexists; eexists; intuition eauto.
  apply_f_equal runsToEndDone; rec_f_equal ltac:(try omega; eauto).
Qed.

(* XXX: NC: not sure which spec I'm supposed to prove, but
[handler_final_mem_matches'] is the only one used, so try to get there
first? *)

Lemma genFaultHandlerMem_spec_Some_None: forall lpc,
  valid_address addrTagResPC m0 ->
  ar = Some (None, lpc) ->
  forall s0,
    HT genFaultHandlerMem
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => upd_m addrTagResPC (labToZ lpc,handlerLabel) m0 =
                     Some m /\
                   s = (1,handlerLabel) ::: s0).
Proof.
  introv Hvalid Har_eq; intros.
  unfold listify_apply_rule.
  rewrite Har_eq.
  unfold genFaultHandlerMem.

  (* Need to exploit early so that existentials can be unified against
  vars introduced here *)
  exploit valid_store; eauto.
  intro H; destruct H.

  eapply HT_strengthen_premise.
  eapply ifNZ_spec_NZ with (v:=1).
  eapply HT_compose_bwd.
  eapply HT_compose_bwd.
  eapply genTrue_spec_wp.
  eapply storeAt_spec_wp.
  eapply ifNZ_spec_Z with (v:=0).
  eapply nop_spec_wp.

  omega.
  omega.
  simpl; intuition; subst; jauto.
Qed.

Lemma genFaultHandlerMem_spec_Some_Some: forall lr lpc,
  valid_address addrTagRes m0 ->
  valid_address addrTagResPC m0 ->
  ar = Some (Some lr, lpc) ->
  forall s0,
    HT genFaultHandlerMem
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s =>
        (exists m', upd_m addrTagRes (labToZ lr,handlerLabel) m0
                    = Some m'
                 /\ upd_m addrTagResPC (labToZ lpc,handlerLabel) m'
                    = Some m)
        /\ s = (1,handlerLabel) ::: s0).
Proof.
  introv HvalidRes HvalidResPC Har_eq; intros.
  unfold listify_apply_rule.
  rewrite Har_eq.
  unfold genFaultHandlerMem.

  (* Need to exploit early so that existentials can be unified against
  vars introduced here *)
  eapply valid_store in HvalidRes.
  destruct HvalidRes as [m' ?].

  eapply valid_address_upd with (m':=m') in HvalidResPC.
  eapply valid_store in HvalidResPC.
  destruct HvalidResPC as [m'' ?]; eauto.

  eapply HT_strengthen_premise.
  eapply ifNZ_spec_NZ with (v:=1).
  eapply HT_compose_bwd.
  eapply HT_compose_bwd.
  eapply genTrue_spec_wp.
  eapply storeAt_spec_wp.
  eapply ifNZ_spec_NZ with (v:=1).
  eapply storeAt_spec_wp.

  omega.
  omega.
  simpl; intuition; subst; jauto.
  eauto.
Qed.

Lemma genFaultHandlerMem_spec_None:
  ar = None ->
  forall s0,
    HT genFaultHandlerMem
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => m = m0 /\
                   s = (0,handlerLabel) ::: s0).
Proof.
  introv Har_eq; intros.
  unfold listify_apply_rule.
  rewrite Har_eq.
  unfold genFaultHandlerMem.

  eapply HT_strengthen_premise.
  eapply ifNZ_spec_Z with (v:=0).
  eapply genFalse_spec.

  reflexivity.
  jauto.
Qed.

(* The irrelevant memory never changes *)
Lemma genFaultHandlerMem_update_cache_spec_rvec:
  valid_address addrTagRes m0 ->
  valid_address addrTagResPC m0 ->
  forall s0,
    HT genFaultHandlerMem
       (fun m s => m = m0 /\
                   s = listify_apply_rule ar s0)
       (fun m s => update_cache_spec_rvec m0 m).
Proof.
  intros.
  unfold update_cache_spec_rvec in *.

  cases ar as Eq_ar.
  destruct p.
  cases o.

  + eapply HT_weaken_conclusion;
    rewrite <- Eq_ar in *.

    eapply genFaultHandlerMem_spec_Some_Some; eauto.

    simpl.
    intros;

    jauto_set_hyps; intros.
    eapply transitivity.
    eapply update_list_spec' with (a' := addrTagRes); eauto.
    eapply update_list_spec' with (a' := addrTagResPC); eauto.

  + eapply HT_weaken_conclusion;
    rewrite <- Eq_ar in *.

    eapply genFaultHandlerMem_spec_Some_None; eauto.

    simpl.
    intros;

    jauto_set_hyps; intros.
    eapply update_list_spec' with (a' := addrTagResPC); eauto.

  + eapply HT_weaken_conclusion;
    rewrite <- Eq_ar in *.

    eapply genFaultHandlerMem_spec_None; eauto.

    simpl; intuition; subst; auto.
Qed.

End FaultHandlerSpec.

End TMUSpecs.
