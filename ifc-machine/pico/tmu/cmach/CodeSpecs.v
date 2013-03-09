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
  (* NC: how to avoid this [Focus]? We need the equality to come later
  the [skipNZ] spec maybe? 
   DD: not sure it's what you're asking for, but giving it as an argument does the job. *)
  intros.
  simpl.
  exists (tl s); intuition.
  destruct s; inversion H0; eauto.

  (* Back at the first (blurred) goal, which is now [1 <> 0] :P *)
  (* omega. *)
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

Lemma HT_fold_constant_premise: forall (C:Prop) c P Q ,
  (C -> HT c P Q) ->
  HT c (fun m s => C /\ P m s) Q.
Proof.
  unfold HT.
  iauto.
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


(* Simplest example: the specification of a single instruction run in
privileged mode *)
Lemma add_spec: forall (z1 z2: Z) (l1 l2: T) (m: memory) (s: stack),
  HT   (Add :: nil)
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

Parameter fetch_rule_impl: fetch_rule_impl_type.
Parameter (opcode: OpCode).
Definition n := projT1 (fetch_rule_impl opcode).
Definition am := projT2 (fetch_rule_impl opcode).
Parameter (vls: Vector.t T n). 
Parameter (pcl: T).
Parameter (m0: memory).

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
  | None               => CData (0, handlerLabel) :: s0
  | Some (None, l2)    => CData (1, handlerLabel) ::
                          CData (0, handlerLabel) ::
                          CData (labToZ l2, handlerLabel) :: s0
  | Some (Some l1, l2) => CData (1, handlerLabel) ::
                          CData (1, handlerLabel) ::
                          CData (labToZ l1, handlerLabel) ::
                          CData (labToZ l2, handlerLabel) :: s0
  end.
(*
  match ar with
  | None => CData (0, handlerLabel) :: s0
  | Some (op, l2) => [ CData (1, handlerLabel) ] ++
                     match op with
                     | None    => [ CData (0, handlerLabel) ]
                     | Some l1 => [ CData (1, handlerLabel)
                                  , CData (labToZ l1, handlerLabel) ]
                     end ++
                     CData (labToZ l2, handlerLabel) :: s0
  end.
*)

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

End TMUSpecs.
