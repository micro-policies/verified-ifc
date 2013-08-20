(* Generic tools for proving properties of (privileged) concrete machine code. *)

Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import LibTactics.
Import ListNotations. 

Require Utils.
Require Import Instr Memory.
Require Import Lattices.
Require Import Concrete.
Require Import CodeGen.
Require Import ConcreteMachine.
Require Import Coq.Arith.Compare_dec.
Require Import ConcreteExecutions.
Require Import EquivDec.
Require Import CodeTriples.

Section CodeSpecs.
Local Open Scope Z_scope.

Notation val := (val privilege).
Notation Atom := (Atom Z privilege).
Notation memory := (Mem.t Atom privilege).
Notation PcAtom := (PcAtom Z).
Notation block := (block privilege).

Variable cblock : block.
Variable stamp_cblock : Mem.stamp cblock = Kernel.

Notation cstep := (cstep cblock).
Notation runsToEscape := (runsToEscape cblock).
Notation HT := (HT cblock).
Notation HTEscape := (HTEscape cblock).

Definition imemory : Type := list Instr.
Definition stack : Type := list CStkElmt.
Definition code := list Instr.
Definition state := CS.
Definition HProp := memory -> stack -> Prop.
(* ================================================================ *)
(* Specs for concrete code *)

Ltac nil_help :=   replace (@nil CEvent) with (op_cons None (@nil CEvent)) by reflexivity.

(* Simplest example: the specification of a single instruction run in
privileged mode *)
Lemma add_spec: forall (z1 z2 z: val) (l1 l2: Z) (m: memory) (s: stack),
  add z1 z2 = Some z ->                  
  HT  [Add]
      (fun m1 s1 => m1 = m /\ s1 = CData (z1,l1) :: CData (z2,l2) :: s)
      (fun m2 s2 => m2 = m /\ s2 = CData (z, handlerTag) :: s).
Proof.
  (* Introduce hyps *)
  intros.
  unfold CodeTriples.HT. intros. intuition.
  eexists.
  eexists.
  eexists.
  intuition. 

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. intuition. 
  
  (* Run an instruction *)
  nil_help.
  econstructor; auto.
  eapply cstep_add_p ; eauto.
Qed.

Lemma sub_spec: forall z1 l1 z2 l2 z, forall m0 s0,
  Memory.sub z1 z2 = Some z ->
  HT [Sub]
     (fun m s => m = m0 /\ s = (z1,l1) ::: (z2,l2) ::: s0)
     (fun m s => m = m0 /\ s = (z,handlerTag) ::: s0).
Proof.
  unfold CodeTriples.HT; intros.
  eexists.
  eexists.
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  nil_help. econstructor; auto.
  eapply cstep_sub_p; eauto.
Qed.

Lemma push_spec: forall v P,
  HT   (Push v :: nil)
       (fun m s => P m (CData (Vint v,handlerTag) :: s))
       P.
Proof.
  intros v P.
  intros imem stk0 c0 fh0 n n' Hcode HP Hn'.
  eexists. eexists. intuition. eauto.
  
  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. simpl in *. intuition. 

  (* Run an instruction *)
  nil_help. econstructor; auto.
  eapply cstep_push_p ; eauto.
Qed.

Lemma push_spec': forall v P,
  HT   (push v)
       P
       (fun m s => head s = Some (CData (Vint v,handlerTag)) /\
                            P m (tail s)).
Proof.
  intros v P.
  intros imem stk0 c0 fh0 n n' Hcode HP Hn'.
  exists (CData (Vint v, handlerTag) :: stk0). eexists c0.
  intuition.
  
  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.

  (* Run an instruction *)
  nil_help.
  econstructor; auto.
  eapply cstep_push_p ; eauto.
  apply Hcode.
Qed.

(* Ghost variable style *)
(* NC: to write a generic instruction-verification tactic, it seems we
   may only need to factor out the specific unfoldings (here [push'])
   and the specific step lemmas (here [cp_push]). *)
Lemma push_spec'': forall v, forall m0 s0,
  HT (push v)
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = CData (Vint v,handlerTag) :: s0).
Proof.
  intros.
  intros imem stk0 c0 fh0 n n' Hcode HP' Hn'.
  eexists.
  eexists.
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold push, code_at in *. intuition.

  (* Run an instruction *)
  nil_help.
  econstructor ; auto.
  eapply cstep_push_p; eauto.
Qed.

Lemma PushCachePtr_spec: forall m0 s0,
  HT [PushCachePtr]
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = CData (Vptr cblock 0,handlerTag) :: s0).
Proof.
  repeat intro.
  do 2 eexists.
  intuition; subst. 

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  nil_help.
  econstructor; auto.
  eapply cstep_push_cache_ptr_p; eauto.
Qed.

Lemma PushCachePtr_spec': forall P,
  HT [PushCachePtr]
     P
     (fun m s => head s = Some (CData (Vptr cblock 0,handlerTag)) /\
                            P m (tail s)).
Proof.
  repeat intro.
  exists ((CData (Vptr cblock 0, handlerTag))::stk0).
  exists mem0.
  simpl in H1.
  intuition; subst. 

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  nil_help.
  econstructor; auto.
  eapply cstep_push_cache_ptr_p; eauto.
Qed.

Lemma load_spec: forall b ofs al v vl, forall m0 s0,
  load b ofs m0 = Some (v,vl) ->
  Mem.stamp b = Kernel ->
  HT [Load]
     (fun m s => m = m0 /\ s = CData (Vptr b ofs,al) :: s0)
     (fun m s => m = m0 /\ s = CData (v,handlerTag) :: s0).
Proof.
  intros b ofs al v vl m0 s0  Hmem.
  intros imem stk0 c0 fh0 n n' Hcode HP' Hn'.
  eexists.
  eexists.
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. intuition. 

  (* Run an instruction *)
  nil_help. econstructor; auto.
  eapply cstep_load_p; eauto.
Qed.

Lemma push_cptr_spec: forall ofs, forall m0 s0,
  HT (push_cptr ofs)
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = CData (Vptr cblock ofs,handlerTag) :: s0).
Proof.
  intros.
  replace (push_cptr ofs) with ([PushCachePtr]++[Push ofs]++[Add]) by auto.
  eapply HT_compose.
  - eapply PushCachePtr_spec.
  - eapply HT_compose.
    + eapply push_spec''.
    + eapply add_spec.
      simpl.
      repeat f_equal; omega.
Qed.

Lemma push_cptr_spec': forall ofs P,
  HT (push_cptr ofs)
     P
     (fun m s => head s = Some (CData (Vptr cblock ofs,handlerTag)) /\
                            P m (tail s)).
Proof.
  intros.
  replace (push_cptr ofs) with ([PushCachePtr]++[Push ofs]++[Add]) by auto.
  eapply HT_compose.
  - eapply PushCachePtr_spec'.
  - eapply HT_compose.
    + eapply push_spec'.
    + simpl.

  unfold CodeTriples.HT. intros. intuition.
  destruct stk0; simpl in H2; inv H2.
  destruct stk0; simpl in H0; inv H0.
  simpl in *.
  exists ((CData (Vptr cblock ofs, handlerTag))::stk0).
  eexists.
  eexists.
  intuition. 
  simpl; eauto.

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. intuition. 
  
  (* Run an instruction *)
  nil_help.
  econstructor; auto.
  eapply cstep_add_p ; eauto.
  simpl; eauto.
  replace (ofs + 0) with ofs by omega.
  constructor; auto.
Qed.

Lemma loadFromCache_spec: forall ofs v vl, forall m0 s0,
  load cblock ofs m0 = Some (v,vl) ->
  HT (loadFromCache ofs)
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = CData (v,handlerTag) :: s0).
Proof.
  intros.
  eapply HT_compose.
  eapply push_cptr_spec.
  eapply load_spec.
  eauto.
  apply stamp_cblock.
Qed.

Lemma pop_spec: forall v vl, forall m0 s0,
  HT [Pop]
     (fun m s => m = m0 /\ s = CData (v,vl) :: s0)
     (fun m s => m = m0 /\ s = s0).
Proof.
  unfold CodeTriples.HT.
  intros.
  eexists.
  eexists.
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_pop_p; eauto.
Qed.

Lemma nop_spec: forall m0 s0,
  HT [Noop]
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = s0).
Proof.
  unfold CodeTriples.HT.
  intros.
  exists s0.
  exists m0.
  intuition.
  simpl in H1; subst.

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. intuition. 
  
  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_nop_p ; eauto.
Qed.

(* NC: to prove that addresses are valid per this definition, we just
   need to know that that the memory is at least as large as the
   [tmuCacheSize] defined in Concrete.v, since we only use
   [valid_address] assumptions for [addrTag*]. *)
Definition valid_address b off (m: memory) :=
  exists v, load b off m = Some v.

Lemma valid_store: forall b off v m,
  valid_address b off m ->
  exists m', store b off v m = Some m'.
Proof.
  unfold valid_address, load, store.
  intros.
  destruct H as [v' Hv].
  destruct (Mem.get_frame m b) as [v''|] eqn:FRAME; try congruence.
  
  exploit valid_update; eauto.
  intros [fr' Hfr'].
  rewrite Hfr'.
  eapply Mem.upd_get_frame; eauto.
Qed. 

Lemma store_spec_wp: forall Q b a al v,
  Mem.stamp b = Kernel ->
  forall m s,
  HT [Store]
     (fun m0 s0 => s0 = (Vptr b a,al) ::: v ::: s /\
                   store b a v m0 = Some m /\
                   Q m s)
     Q.
Proof.
  unfold CodeTriples.HT.
  intros.
  jauto_set_hyps; intros.
  eexists.
  eexists.
  intuition; subst.
  eauto.

  (* Load an instruction *)
  unfold code_at in *. intuition.

  (* Run an instruction *)
  nil_help. econstructor; auto.
  eapply cstep_store_p; eauto.
Qed.

Lemma store_spec: forall b a al v vl m s,
  Mem.stamp b = Kernel ->
  HT [Store]
     (fun m0 s0 => m0 = m /\
                   s0 = (Vptr b a,al) ::: (v,vl) ::: s /\
                   valid_address b a m) (* NC: better to move this outside? *)
     (fun m1 s1 => s1 = s /\
                   store b a (v,vl) m = Some m1).
Proof.
  unfold CodeTriples.HT.
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
  nil_help. econstructor; auto.
  eapply cstep_store_p; eauto.
Qed.

Lemma storeAt_spec: forall a v vl m s,
  HT (storeAt a)
     (fun m0 s0 => m0 = m /\
                   s0 = (v,vl) ::: s /\
                   valid_address cblock a m)
     (fun m1 s1 => s1 = s /\
                   store cblock a (v,vl) m = Some m1).
Proof.
  intros.
  eapply HT_compose.
  eapply HT_consequence'.
  eapply push_cptr_spec.
  intuition; eauto.
  intuition; eauto.
  Focus 2. (* Eeek! *)
  eapply store_spec.
  apply stamp_cblock.
  intuition; eauto.
  jauto.
Qed.


(* NC: [valid_address a m0] implies [upd_m] succeeds *)
Lemma storeAt_spec_wp: forall a vl Q,
  forall m s,
  HT (storeAt a)
     (fun m0 s0 => s0 = vl ::: s /\
                   store cblock a vl m0 = Some m /\
                   Q m s)
     Q.
Proof.
  intros.
  eapply HT_compose.
  eapply push_cptr_spec'.
  eapply HT_strengthen_premise.
  eapply store_spec_wp.
  apply stamp_cblock.
  intuition; eauto.
  destruct s0; simpl in *.
  - false.
  - subst.
    unfold value in *.
    inversion H0; subst.
    reflexivity.
Qed.

Lemma skipNZ_continuation_spec_NZ: forall c P v l,
  v <> 0 ->
  HT   (skipNZ (length c) ++ c)
       (fun m s => (exists s', s = CData (Vint v,l) :: s' 
                               /\ P m s'))
       P.
Proof.
  intros c P v l Hv.
  intros imem stk0 c0 fh0 n n' Hcode HP Hn'.
  destruct HP as [stk1 [H_stkeq HPs']].
  exists stk1. exists c0. 
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. simpl in *. intuition. fold code_at in *.

  (* Run an instruction *) 
  nil_help.   eapply rte_step; eauto. 
  match goal with 
    | |- context[n + ?z] =>
      replace (n + z) with (if v =? 0 then n + 1 else n + z)
  end.
  eapply cstep_branchnz_p ; eauto. 

  assert (Hif: v =? 0 = false) by (destruct v; [omega | auto | auto]).  
  rewrite Hif.
  reflexivity.
Qed.

Lemma skipNZ_spec_Z: forall n P v l,
  v = 0 ->
  HT   (skipNZ n)
       (fun m s => (exists s', s = CData (Vint v,l) :: s' 
                               /\ P m s'))
       P.
Proof.
  intros c P v l Hv.
  intros imem stk0 c0 fh n n' Hcode HP Hn'.
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
  eapply rte_step; auto.

  replace (n + 1) with 
    (if 0 =? 0 then n + 1 else n + Z.pos (Pos.of_succ_nat c)); try reflexivity.
  eapply cstep_branchnz_p ; eauto. 
Qed.

Lemma skipNZ_continuation_spec_Z: forall c P Q v l,
  v = 0 ->
  HT   c P Q  ->
  HT   (skipNZ (length c) ++ c)
       (fun m s => (exists s', s = CData (Vint v,l) :: s' 
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
       (fun m s => (exists s', s = CData (Vint v,l) :: s' /\ P m s'))
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
       (fun m s => (exists s', s = CData (Vint v,l) :: s' /\ P m s'))
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
       (fun m s => ((v <> 0 -> exists s', s = CData (Vint v,l) :: s' /\ Pt m s') /\
                    (v =  0 -> exists s', s = CData (Vint v,l) :: s' /\ Pf m s')))
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
       (fun m s => (exists s', s = CData (Vint v,l) :: s' /\
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
       (fun m s => (exists v l s', s = CData (Vint v,l) :: s' /\
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
Lemma ite_spec: forall c t f (P Pt Pf: HProp) Q,
  let P' := fun m s => exists v l s', s = (Vint v,l) ::: s' /\
                                      (v <> 0 -> Pt m s') /\
                                      (v =  0 -> Pf m s') in
  HT   c P P' ->
  HT   t Pt Q ->
  HT   f Pf Q ->
  HT   (ite c t f) P Q.
Proof.
  intros c t f P Pt Pf Q P' HTc HTt HTf.
  unfold ite.
  eapply HT_compose.
  apply HTc.
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
  HT c P  (fun m s => m = m0 /\ s = (Vint v,handlerTag) ::: s0) ->
  (v <> 0 -> HT t P Q) ->
  (v =  0 -> HT f P Q) ->
  HT (ite c t f) P Q.
Proof.
  introv HTc HZ HNZ.
  eapply ite_spec with (Pt := fun m s => v <> 0 /\ m = m0 /\ s = s0)
                       (Pf := fun m s => v =  0 /\ m = m0 /\ s = s0).
  eauto.
  eapply HT_weaken_conclusion.
  eauto.

  introv Heq.
  simpl in Heq.
  jauto.

  eapply HT_fold_constant_premise; auto.
  eapply HT_fold_constant_premise; auto.
Qed.

Lemma cases_spec_base: forall d P Q,
  HT   d P Q -> HT   (cases nil d) P Q.
Proof.
  auto.
Qed.

Lemma cases_spec_step: forall c b cbs d P (Pt Pf Q: HProp),
  let P' := fun m s => exists v l s', s = (Vint v,l) ::: s' /\
                                      (v <> 0 -> Pt m s') /\
                                      (v =  0 -> Pf m s') in
  HT   c P P' ->
  HT   b Pt Q ->
  HT   (cases cbs d) Pf Q ->
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
                        s = CData (Vint (vc m0 s0), handlerTag) :: s0)) ->
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
  eapply HT_weaken_conclusion.
  exact Hcm0s0.

  intuition.
  exists (vc m0 s0).
  exists handlerTag.
  exists s0.
  intuition; subst; auto.

  apply (HT_consequence' _ _ _ _ _ _ Hb); intuition.
  elimtype False; jauto.

  apply (HT_consequence' _ _ _ _ _ _ Hcbs); intuition.
  elimtype False; jauto.
Qed.

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
                           s = CData (Vint (v m0 s0), handlerTag) :: s0).
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
  eapply HT_weaken_conclusion.
  exact Hcm0s0.

  intuition.
  exists (vc m0 s0).
  exists handlerTag.
  exists s0.
  intuition; subst; auto.

  apply (HT_consequence' _ _ _ _ _ _ (Hb m0 s0)); intuition.
  elimtype False; jauto.

  fold cases.
  apply (HT_consequence' _ _ _ _ _ _ (Hcbs m0 s0)); intuition.
  elimtype False; jauto.
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
     (fun m s => m = m0 /\ s = (Vint 1,handlerTag) ::: s1).
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
     (fun m s => m = m0 /\ s = CData (Vint (boolToZ b1),handlerTag) ::
                               CData (Vint (boolToZ b2),handlerTag) :: s0)
     (fun m s => m = m0 /\ s = CData (Vint (boolToZ (andb b1 b2)),handlerTag) :: s0).
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
     (fun m s => m = m0 /\ s = CData (Vint (boolToZ b1),handlerTag) ::
                               CData (Vint (boolToZ b2),handlerTag) :: s0)
     (fun m s => m = m0 /\ s = CData (Vint (boolToZ (orb b1 b2)),handlerTag) :: s0).
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
     (fun m s => m = m0 /\ s = CData (Vint v, handlerTag) :: s0)
     (fun m s => m = m0 /\ 
                 s = CData (Vint (boolToZ (v =? 0)),handlerTag) :: s0).
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
     (fun m s => m = m0 /\ s = (Vint (boolToZ b), handlerTag) ::: s0)
     (fun m s => m = m0 /\ s = (Vint (boolToZ (negb b)), handlerTag) ::: s0).
Proof.
  intros.
  eapply HT_weaken_conclusion.
  - eapply genNot_spec_general.
  - cases b; auto.
Qed.

Lemma genImpl_spec: forall b1 b2, forall m0 s0,
  HT genImpl
     (fun m s => m = m0 /\ s = CData (Vint (boolToZ b1),handlerTag) ::
                               CData (Vint (boolToZ b2),handlerTag) :: s0)
     (fun m s => m = m0 /\ s = CData (Vint (boolToZ (implb b1 b2)),handlerTag) :: s0).
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
        (fun m s => m = m0 /\ s = (Vint v1,handlerTag) ::: s0)) ->
  (forall s0,
     HT c2
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (Vint v2,handlerTag) ::: s0)) ->
  (forall s0,
     HT (genTestEqual c1 c2)
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (Vint (boolToZ (v1 =? v2)),handlerTag) ::: s0)).
Proof.
  intros.
  unfold genTestEqual.
  eapply HT_compose; eauto.
  eapply HT_compose; eauto.
  eapply HT_compose.
  eapply sub_spec.
  simpl; eauto.
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

Lemma HT_compose_bwd:
  forall (c1 c2 : code) (P Q R : HProp),
    HT c2 Q R -> HT c1 P Q -> HT (c1 ++ c2) P R.
Proof.
  intros; eapply HT_compose; eauto.
Qed.

Lemma valid_address_upd: forall b a b' a' vl m m',
  valid_address b a m ->
  store b' a' vl m = Some m' ->
  valid_address b a m'.
Proof.
  unfold valid_address; intuition.
  destruct H.
  unfold load, store in *.
  destruct (b == b').
  - inv e.
    destruct (Mem.get_frame m b') eqn:E; try congruence.
    destruct (upd_m a' vl l) eqn:E'; try congruence.
    inv H0.
    rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H2).
    destruct (equiv_dec b'); try congruence.
    unfold upd_m, read_m in *.
    destruct (a <? 0); try congruence.
    destruct (a' <? 0); try congruence.
    destruct (eq_nat_dec (Z.to_nat a) (Z.to_nat a')).
    + rewrite e0 in *; erewrite update_list_spec; eauto.
    + erewrite <- update_list_spec2; eauto.
  - destruct (Mem.get_frame m b) eqn:E; try congruence.
    destruct (Mem.get_frame m b') eqn:E'; try congruence.
    destruct (upd_m a' vl l0) eqn:E0; try congruence.
    rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H0).
    destruct (equiv_dec b'); try congruence.
    rewrite E.
    eauto.
Qed.

(* DP: TODO ???
Lemma store_twice_test: forall a1 a2 v1 v2 vl1 vl2,
  a1 <> a2 ->
  forall m s,
  valid_address a1 m ->
  valid_address a2 m ->
  HT (storeAt a1 ++ storeAt a2)
     (fun m0 s0 => m0 = m /\
                   s0 = CData (v1, vl1) :: CData (v2,vl2) :: s)
     (fun m1 s1 => s1 = s /\
                   exists m', upd_m a1 (v1,vl1) m = Some m' /\
                              upd_m a2 (v2,vl2) m' = Some m1).
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
*)

(* Follow from a more general [push'_spec_wp]. *)
Lemma genTrue_spec_wp: forall Q,
  HT genTrue
     (fun m s => Q m ((Vint 1,handlerTag):::s))
     Q.
Proof.
  eapply push_spec.
Qed.

Lemma genFalse_spec_wp: forall Q,
  HT genFalse
     (fun m s => Q m ((Vint 0,handlerTag):::s))
     Q.
Proof.
  eapply push_spec.
Qed.

Lemma nop_spec_wp: forall Q,
  HT [Noop] Q Q.
Proof.
  unfold CodeTriples.HT; simpl; intros.
  eexists; eexists; intuition eauto. subst.

  (* Run an instruction *)
  eapply rte_step; eauto.
  eapply cstep_nop_p ; eauto.
Qed.

Lemma ret_specEscape: forall raddr (P: HProp),
  HTEscape raddr [Ret]
    (fun m s => exists s', s = (CRet raddr false false::s') /\ P m s')
    (fun m s => (P m s , Success)).
Proof.
  intros. cases raddr; subst.
  unfold CodeTriples.HTEscape. intros. intuition.
  jauto_set_hyps; intuition.
  repeat eexists.
  eauto.

  (* Load an instruction *)
  subst.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_success; auto.
  eapply ruu_end; simpl; eauto.
  eapply cstep_ret_p; auto.
  eapply cptr_done.
Qed.

Lemma jump_specEscape_Failure: forall tag raddr (P: HProp),
  HTEscape raddr [Jump]
           (fun m s => exists s0, (Vint (-1), tag) ::: s0 = s /\ P m s0)
           (fun m s => (P m s , Failure)).
Proof.
  intros.
  unfold CodeTriples.HTEscape. intros.
  jauto_set_hyps; intuition.
  repeat eexists.
  eauto.

  (* Load an instruction *)
  subst.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_fail; auto.
  eapply rte_step; eauto.
  eapply cstep_jump_p; auto.
  simpl; eauto; omega.
Qed.

Lemma skipNZ_specEscape: forall r c1 c2 v P1 P2 Q,
  (v =  0 -> HTEscape r c1 P1 Q) ->
  (v <> 0 -> HTEscape r c2 P2 Q) ->
  HTEscape r ((skipNZ (length c1) ++ c1) ++ c2)
           (fun m s => exists s0, s = (Vint v, handlerTag) ::: s0 /\
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
           (fun m s => exists s0, s = (Vint v, handlerTag) ::: s0 /\
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
