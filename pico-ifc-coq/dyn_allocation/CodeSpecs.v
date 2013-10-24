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

Local Notation val := (val privilege).
Local Notation Atom := (Atom val privilege).
Local Notation memory := (Mem.t Atom privilege).
Local Notation PcAtom := (PcAtom val).
Local Notation block := (block privilege).
Definition HProp := memory -> stack -> Prop.

Definition extension_comp (P : HProp) :=
  forall m1 m2 s, P m1 s -> extends m1 m2 -> P m2 s.

Ltac go_match :=
  try match goal with
    | H1: extends ?m1 ?m2,
      H2: extends ?m2 ?m3 |- _ => assert (Hext_trans: extends m1 m3) by (unfold extends in *; eauto)
  end;
  let H := fresh "H" in
  try (simpl; intros ? ? H);
    repeat match goal with
             | [H: match ?sss with _ => _ end |- _ ] =>
               destruct sss ; intuition ;
               try (substs; eauto)
           end.

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

Section CodeSpecs.
Local Open Scope Z_scope.

Variable cblock : block.
Variable stamp_cblock : Mem.stamp cblock = Kernel.
Variable table : CSysTable.

Notation cstep := (cstep cblock table).
Notation runsToEscape := (runsToEscape cblock table).
Notation HT := (HT cblock table).
Notation HTT := (HTT cblock table).
Notation HTEscape := (HTEscape cblock table).

(* To stop struggling with [replace]s *)
Lemma cstep_branchnz_p' : forall m fh i s pcv pcl offv av al pc',
       read_m pcv fh = Some (BranchNZ offv) ->
       pc' = (if av =? 0 then pcv + 1 else pcv + offv) ->
       cstep (CState m fh i ((Vint av, al) ::: s) (pcv, pcl) true) Silent
             (CState m fh i s (pc',handlerTag) true).
Proof.
  intros. subst.
  econstructor (solve [eauto]).
Qed.

Definition imemory : Type := list Instr.
Definition stack : Type := list CStkElmt.
Definition code := list Instr.
Definition state := CS.

(* ================================================================ *)
(* Specs for concrete code *)

Ltac nil_help :=   replace (@nil CEvent) with (op_cons Silent (@nil CEvent)) by reflexivity.

Lemma add_spec :
  HTT [Add]
      (fun Q m0 s0 =>
         exists v1 t1 v2 t2 vr s,
           s0 = (v1,t1) ::: (v2,t2) ::: s /\
           add v1 v2 = Some vr /\
           Q m0 ((vr,handlerTag) ::: s)).
Proof.
  intros Q.
  eapply HT_forall_exists. intros v1.
  eapply HT_forall_exists. intros t1.
  eapply HT_forall_exists. intros v2.
  eapply HT_forall_exists. intros t2.
  eapply HT_forall_exists. intros vr.
  eapply HT_forall_exists. intros s.
  apply HT_strengthen_premise with (fun m0 s0 =>
                                      add v1 v2 = Some vr /\
                                      s0 = (v1, t1) ::: (v2, t2) ::: s /\
                                      Q m0 ((vr, handlerTag) ::: s)); try solve [split_vc].
  eapply HT_fold_constant_premise. intros H.

  unfold CodeTriples.HT.
  intros imem stk0 mem0 fh n n' Hcode (Hstk & H') Hn'.
  subst.
  eexists. eexists. split. eauto.

  (* Load an instruction *)
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_add_p; eauto.
Qed.

Lemma sub_spec :
  HTT [Sub]
     (fun Q m0 s0 =>
        exists v1 t1 v2 t2 vr s,
          s0 = (v1,t1) ::: (v2,t2) ::: s /\
          Memory.sub v1 v2 = Some vr /\
          Q m0 ((vr,handlerTag) ::: s)).
Proof.
  intros Q.
  eapply HT_forall_exists. intros v1.
  eapply HT_forall_exists. intros t1.
  eapply HT_forall_exists. intros v2.
  eapply HT_forall_exists. intros t2.
  eapply HT_forall_exists. intros vr.
  eapply HT_forall_exists. intros s.
  apply HT_strengthen_premise with (fun m0 s0 =>
                                      Memory.sub v1 v2 = Some vr /\
                                      s0 = (v1, t1) ::: (v2, t2) ::: s /\
                                      Q m0 ((vr, handlerTag) ::: s)); try solve [split_vc].
  eapply HT_fold_constant_premise. intros H.

  unfold CodeTriples.HT.
  intros imem stk0 mem0 fh n n' Hcode (Hstk & H') Hn'.
  subst.
  eexists. eexists. split. eauto.

  (* Load an instruction *)
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_sub_p; eauto.
Qed.

Lemma dup_spec:
  forall n,
  HTT [Dup n]
      (fun Q m s => exists x, index_list n s = Some x /\ Q m (x :: s)).
Proof.
  intros n Q.
  unfold CodeTriples.HT.
  intros imem mem0 stk0 fh0 n0 n0' Hcode [x [HI HP]] Hn'.
  eexists. eexists. intuition. eauto.

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. simpl in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_dup_p ; eauto.
Qed.

Lemma swap_spec: forall n,
  HTT [Swap n]
      (fun Q m s => exists y s0 x s', s = y::s0 /\
                                      index_list n s = Some x /\
                                      update_list n y (x::s0) = Some s' /\
                                      Q m s').
Proof.
  intros n Q.
  unfold CodeTriples.HT.
  intros imem mem0 stk0 fh0 n0 n0' Hcode [y [s0 [x [s' [HE [HI [HU HP]]]]]]] Hn'.
  eexists. eexists. intuition. eauto.

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. simpl in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_swap_p ; eauto.
Qed.

Lemma push_spec: forall v,
  HTT [Push v]
      (fun Q m s => Q m (CData (Vint v,handlerTag) :: s)).
Proof.
  intros Q v.
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

Lemma PushCachePtr_spec :
  HTT [PushCachePtr]
      (fun Q m s =>
         Q m (CData (Vptr (cblock, 0),handlerTag) :: s)).
Proof.
  repeat intro.
  exists ((CData (Vptr (cblock, 0), handlerTag))::stk0).
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

Lemma push_cptr_spec :
  forall v,
    HTT (push_cptr v)
        (fun Q m s => Q m ((Vptr (cblock, v), handlerTag) ::: s)).
Proof.
  intros.
  intros Q imem mem0 stk0 c0 fh0 n Hcode HP' Hn'.
  eexists. eexists.

  subst.
  unfold push_cptr, code_at in *.
  intuition.
  Focus 2.
  do 3 try (eapply rte_step); eauto.
  eapply cstep_push_cache_ptr_p; eauto.
  reflexivity.
  eapply cstep_push_p; eauto.
  reflexivity.
  simpl.
  replace (fh0 + 3) with (fh0 + 1 + 1 + 1) by omega.
  eapply cstep_add_p; eauto.
  reflexivity.
  simpl. replace (v + 0) with v by omega.
  assumption.
Qed.

Lemma load_spec :
  HTT [Load]
      (fun Q m s0 => exists p t x s,
                       s0 = (Vptr p,t) ::: s /\
                       Mem.stamp (fst p) = Kernel /\
                       load p m = Some x /\
                       Q m (x ::: s)).
Proof.
  intros Q. eapply HT_forall_exists.
  intros p. eapply HT_forall_exists.
  intros t. eapply HT_forall_exists.
  intros x. eapply HT_forall_exists.
  intros s0.
  intros imem mem0 stk0 fh0 n n' Hcode HP' Hn'.
  eexists.
  eexists.
  intuition eauto.

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_load_p; eauto.
Qed.

Lemma unpack_spec :
  HTT [Unpack]
      (fun Q m s => exists x l s0,
                      s = (x,l):::s0 /\
                      Q m ((l,handlerTag):::(x,handlerTag):::s0)).
Proof.
  intros Q.
  unfold CodeTriples.HT. intros. destruct H0 as [x [l [s0 [? ?]]]].
  eexists.
  eexists.
  split.  apply H2.

  (* Load an instruction *)
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  simpl in H1.  subst.
  eapply cstep_unpack_p; eauto.
Qed.

Lemma pack_spec :
  HTT [Pack]
      (fun Q m s => exists x t l l0 s0,
                      s = (l,t):::(x,l0):::s0 /\
                      Q m ((x,l):::s0)).
Proof.
  intros Q.
  unfold CodeTriples.HT. intros. destruct H0 as [x [t [l [l0 [s0 [? ?]]]]]].
  eexists.
  eexists.
  split.  apply H2.

  (* Load an instruction *)
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  simpl in H1.  subst.
  eapply cstep_pack_p; eauto.
Qed.

Lemma loadFromCache_spec: forall ofs,
  HTT (loadFromCache ofs)
      (fun Q m s =>
         exists v,
           value_on_cache cblock m ofs v /\
           forall t, Q m (CData (v, t) :: s)).
Proof.
  intros.
  unfold loadFromCache.
  eapply HTT_strengthen_premise.
  { eapply HTT_compose; try eapply push_cptr_spec.
    eapply load_spec. }
  intros Q m s (? & [] & POST). subst.
  repeat eexists; eauto.
Qed.

Lemma pop_spec:
  HTT [Pop]
      (fun Q m s => exists v vl s0, s = (v,vl):::s0 /\ Q m s0).
Proof.
  intros Q.
  unfold CodeTriples.HT.
  intros. destruct H0 as [v [vl [s0 [P1 P2]]]].
  eexists.
  eexists.
  split; eauto.

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_pop_p; eauto.
Qed.

Lemma nop_spec: HTT [Noop] (fun Q => Q).
Proof.
  intros Q.
  unfold CodeTriples.HT.
  intros.
  exists stk0.
  exists mem0.
  intuition.
  simpl in H1; subst.

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *.
  intuition.

  (* Run an instruction *)
  eapply rte_step; eauto.
  eapply cstep_nop_p ; eauto.
Qed.

Lemma store_spec :
  HTT [Store]
      (fun Q (m0 : memory) (s0 : stack) =>
         exists p al v m s,
           Mem.stamp (fst p) = Kernel /\
           s0 = (Vptr p, al) ::: v ::: s /\ store p v m0 = Some m /\ Q m s).
Proof.
  intros Q.
  eapply HT_forall_exists. intro. eapply HT_forall_exists.
  intro. eapply HT_forall_exists. intro. eapply HT_forall_exists.
  intro. eapply HT_forall_exists.
  intro. apply HT_fold_constant_premise. intro.
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

Lemma storeAt_spec: forall a,
  HTT (storeAt a)
      (fun Q m0 s0 => exists vl s m,
                        s0 = vl ::: s /\
                        store (cblock, a) vl m0 = Some m /\
                        Q m s).
Proof.
  intros.
  eapply HTT_strengthen_premise.
  { eapply HTT_compose; try eapply push_cptr_spec.
    eapply store_spec; eauto. }
  intuition; eauto. destruct H as [vl [s0 [m0 Hint]]]. intuition; substs.
  do 5 eexists; intuition; eauto.
Qed.

Lemma alloc_spec :
  HTT [Alloc]
      (fun Q m0 s0 => exists s t xv xl cnt,
                        s0 = (Vint cnt,t) ::: (xv, xl) ::: s /\
                        cnt >= 0 /\
                        (forall b m,
                           c_alloc Kernel cnt (xv,xl) m0 = Some (b, m) ->
                           Q m ((Vptr (b, 0),handlerTag):::s))).
Proof.
  intros Q.
  unfold CodeTriples.HT. intros.
  destruct H0 as (s & t & xv & xl & cnt & ? & ? & ?).
  subst.

  assert (ALLOC : exists b m',
                    c_alloc Kernel cnt (xv,xl) mem0 = Some (b, m')).
  { unfold c_alloc, alloc, zreplicate.
    destruct (Z_lt_dec cnt 0); try omega.
    match goal with
      | |- context [Some ?p = Some _] => destruct p
    end.
    eauto. }

  destruct ALLOC as (b & m' & ALLOC).

  repeat eexists; eauto.

  (* Load an instruction *)
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_alloc_p; eauto.
Qed.

Lemma skipNZ_continuation_spec_NZ: forall c P v,
  v <> 0 ->
  HT   (skipNZ (length c) ++ c)
       (fun m s => (exists s' l, s = CData (Vint v,l) :: s'
                                 /\ P m s'))
       P.
Proof.
  intros c P v Hv.
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

Lemma skipNZ_spec_Z: forall n P v,
  v = 0 ->
  HT   (skipNZ n)
       (fun m s => (exists s' l, s = CData (Vint v,l) :: s'
                                 /\ P m s'))
       P.
Proof.
  intros c P v Hv.
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

Lemma skipNZ_continuation_spec_Z: forall c P Q v,
  v = 0 ->
  HT   c P Q  ->
  HT   (skipNZ (length c) ++ c)
       (fun m s => (exists s' l, s = CData (Vint v,l) :: s'
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
  eapply HT_strengthen_premise.
  { unfold skip.
    rewrite app_ass.
    eapply HT_compose; try eapply push_spec.
    eapply skipNZ_continuation_spec_NZ with (v:= 1); omega. }
  simpl. intros.
  repeat eexists. auto.
Qed.

Lemma ifNZ_spec_Z: forall v t f P Q,
  HT   f P Q ->
  v = 0 ->
  HT   (ifNZ t f)
       (fun m s => (exists s' l, s = CData (Vint v,l) :: s' /\ P m s'))
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

Lemma ifNZ_spec_NZ: forall v t f P Q,
  HT   t P Q ->
  v <> 0 ->
  HT   (ifNZ t f)
       (fun m s => (exists s' l, s = CData (Vint v,l) :: s' /\ P m s'))
       Q.
Proof.
  intros v l t f P Q HTt Hveq0.
  unfold ifNZ.
  rewrite <- app_ass.
  eapply HT_compose; eauto.
  apply skipNZ_continuation_spec_NZ; auto.
Qed.

Lemma ifNZ_spec_helper: forall v t f Pt Pf Q,
  HT   t Pt Q ->
  HT   f Pf Q ->
  HT   (ifNZ t f)
       (fun m s => ((v <> 0 -> exists s' l, s = CData (Vint v,l) :: s' /\ Pt m s') /\
                    (v =  0 -> exists s' l, s = CData (Vint v,l) :: s' /\ Pf m s')))
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

Lemma ifNZ_spec: forall t f Pt Pf Q,
  HT   t Pt Q ->
  HT   f Pf Q ->
  HT   (ifNZ t f)
       (fun m s => (exists v l s', s = CData (Vint v,l) :: s' /\
                                   (v <> 0 -> Pt m s') /\
                                   (v =  0 -> Pf m s')))
       Q.
Proof.
  intros t f Pt Pf Q HTt HTf.
  eapply HT_forall_exists. intros v.
  eapply HT_forall_exists. intros l.
  eapply HT_forall_exists. intros s'.
  eapply HT_strengthen_premise.
  eapply ifNZ_spec_helper; eauto.
  intros m s (? & H1 & H2). subst.
  destruct (dec_eq v 0); subst; intuition;
    eexists; intuition eauto.
Qed.

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
  apply ifNZ_spec.
  auto.
  auto.
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

  apply (HT_consequence' _ _ _ _ _ _ _ Hb); intuition.
  elimtype False; jauto.

  apply (HT_consequence' _ _ _ _ _ _ _ Hcbs); intuition.
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
                           exists t, s = CData (Vint (v m0 s0), t) :: s0).
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

  intros m s (POST & ? & t & ?). subst.
  exists (vc m0 s0).
  exists t.
  exists s0.
  intuition; subst; auto.

  apply (HT_consequence' _ _ _ _ _ _ _ (Hb m0 s0)); intuition.
  elimtype False; jauto.

  fold cases.
  apply (HT_consequence' _ _ _ _ _ _ _ (Hcbs m0 s0)); intuition.
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

Section GT_ext.

Definition GT_ext (c: code) (P: HProp) (Q: GProp) :=
  forall m0 s0,
    HT c
       (fun m s => P m0 s0 /\ extends m0 m /\ s = s0)
       (Q m0 s0).

Lemma GT_consequence'_ext:
  forall (c : code) (P' P: HProp) (Q Q': GProp),
    GT_ext c P Q ->
    (forall m s, P' m s -> P m s) ->
    (forall m0 s0 m s, P m0 s0 -> Q m0 s0 m s -> Q' m0 s0 m s) ->
    GT_ext c P' Q'.
Proof.
  unfold GT_ext; intros.
  eapply HT_consequence'; jauto.
Qed.

Lemma cases_spec_base_GT_ext_specialized: forall cnil P Qnil,
  GT_ext cnil P Qnil ->
  GT_ext (cases [] cnil) P Qnil.
Proof.
unfold GT_ext; intros; eapply cases_spec_base.
  eapply HT_strengthen_premise; eauto.
Qed.

Definition GT_push_v_ext (c: code) (P: HProp) (v: HFun): Prop :=
  GT_ext c P (fun m0 s0 m s => exists t, P m0 s0 /\
                               extends m0 m /\
                               s = CData (Vint (v m0 s0), t) :: s0).
Definition GT_guard_v_ext (b: code) (P: HProp) (v: HFun) (Q: GProp): Prop :=
  GT_ext b (fun m s => P m s /\ v m s <> 0) Q.

Lemma cases_spec_step_GT_ext_specialized: forall c v b cbs cnil P Qb Qcbs,
  GT_push_v_ext c P v ->
  GT_guard_v_ext b P v Qb ->
  GT_ext (cases cbs cnil) P Qcbs ->
  GT_ext (cases ((c,b)::cbs) cnil)
     P
     (fun m0 s0 m s =>   (v m0 s0 <> 0 -> Qb m0 s0 m s)
                         /\ (v m0 s0 = 0 -> Qcbs m0 s0 m s)).
Proof.
  intros c vc b cbs d P Qb Qcbs Hc Hb Hcbs.
  intros m0 s0.
  pose (Hc m0 s0) as Hcm0s0.
  eapply ite_spec with (Pt := (fun m s => P m0 s0 /\ extends m0 m /\ s = s0 /\ vc m0 s0 <> 0))
                       (Pf := (fun m s => P m0 s0 /\ extends m0 m /\ s = s0 /\ vc m0 s0 =  0)).
  - eapply HT_weaken_conclusion.
    eapply Hc.
    go_match.
    split_vc.
  - eapply HT_consequence'.
    + eapply Hb; eauto.
    + intros. intuition.
      * eapply H0.
      * elimtype False; jauto.
      * auto.
      * auto.
    + intros.
      destruct H as [m' [s' [HPm0s0 [Hextm0 [Hs' Hcond]]]]]. substs.
      split; eauto.
      intuition.
  - fold cases.
    eapply HT_consequence'.
    eapply Hcbs.
    simpl. iauto.
    intros. intuition.
    elimtype False; jauto.
Qed.

Section IndexedCasesSpec_EXT.

Variable cnil: code.
Variable Qnil: GProp.
Variable I: Type.
Variable genC genB: I -> code.
Variable genQ: I -> GProp.
Variable genV: I -> HFun.

(* XXX: make these folds ? *)
Definition indexed_post_ext: (list I) -> GProp :=
  fix f (indices: list I) :=
    fun m0 s0 m s =>
      match indices with
      | []            => Qnil m0 s0 m s
      | i :: indices' =>
                         (genV i m0 s0 <> 0 -> genQ i m0 s0 m s) /\
                         (genV i m0 s0 =  0 -> f indices' m0 s0 m s)
      end.

Variable P: HProp.
Definition indexed_hyps_ext: (list I) -> Prop :=
  fix f (indices: list I) :=
    match indices with
    | []            => True
    | i :: indices' => GT_push_v_ext (genC i) P (genV i) /\
                       GT_guard_v_ext (genB i) P (genV i) (genQ i) /\
                       f indices'
    end.

Lemma indexed_cases_spec_ext: forall is,
  GT_ext cnil P Qnil ->
  indexed_hyps_ext is ->
  GT_ext (indexed_cases cnil genC genB is)
     P
     (indexed_post_ext is).
Proof.
  induction is; intros.
  - eapply cases_spec_base_GT_ext_specialized; eauto.
  - simpl in *.
    eapply cases_spec_step_GT_ext_specialized; iauto.
Qed.

End IndexedCasesSpec_EXT.

End GT_ext.

Lemma some_spec:
  forall c T,
    HTT c T ->
    HTT (some c) (fun Q => T (fun m s => Q m ((Vint 1,handlerTag) ::: s))).
Proof.
  intros.
  unfold some.
  eapply HTT_compose; eauto.
  eapply push_spec.
Qed.

Definition none_spec     := push_spec.
Definition genTrue_spec  := push_spec.
Definition genFalse_spec := push_spec.

Definition ZtoBool (z:Z) :=  negb (z =? 0).
Definition valToBool (v : val) :=
  match v with
    | Vint 0 => false
    | _ => true
  end.

Lemma genEq_spec :
  HTT genEq
      (fun Q m s => exists v1 t1 v2 t2 s0 ,
                      s = (v1,t1):::(v2,t2):::s0 /\
                      Q m ((val_eq v1 v2,handlerTag):::s0)).
Proof.
  intros Q. unfold genEq.
  intros imem stk0 mem0 fh n n' CODE PRE Hn'. subst.
  simpl in CODE. destruct CODE as [CODE _].
  destruct PRE as (v1 & t1 & v2 & t2 & s0 & H1 & H2). subst.

  repeat eexists; eauto.

  eapply rte_step; eauto.

  eapply cstep_eq_p; eauto.
Qed.

Lemma val_eq_int :
  forall z1 z2,
    val_eq (Vint z1) (Vint z2) = Vint (boolToZ (z1 =? z2)).
Proof.
  unfold val_eq.
  intros.
  destruct (equiv_dec (Vint z1) (Vint z2)) as [E | E].
  - inv E. rewrite Z.eqb_refl. reflexivity.
  - assert (E' : z1 <> z2) by congruence.
    rewrite <- Z.eqb_neq in E'.
    rewrite E'. reflexivity.
Qed.

Definition andv (v1 v2 : val) : val :=
  if valToBool v1 then v2 else Vint 0.

Lemma genAnd_spec: forall (Q:memory -> stack -> Prop),
  HT genAnd
     (fun m s => exists v1 t1 v2 t2 s0,
                   s = (v1,t1):::(v2,t2):::s0 /\
                   forall t, Q m ((andv v1 v2,t):::s0))
     Q.
Proof.
  intros.
  eapply HT_forall_exists.  intro v1.
  eapply HT_forall_exists.  intro t1.
  eapply HT_forall_exists.  intro v2.
  eapply HT_forall_exists.  intro t2.
  eapply HT_forall_exists.  intro s0.
  unfold genAnd, andv.
  destruct (valToBool v1) eqn:E.
  - assert (v1 <> Vint 0). { intro. subst. unfold valToBool in E. congruence. }
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec.
      eapply HT_compose; try eapply genEq_spec.
      eapply ifNZ_spec_Z with (v:=0); eauto.
      apply nop_spec.
    + intros m s [H1 H2]. subst.
      do 6 eexists. do 2 (split; eauto).
      do 2 eexists. split; repeat f_equal; eauto.
      unfold val_eq.
      destruct (equiv_dec (Vint 0) v1); congruence.
  - assert (v1 = Vint 0). { unfold valToBool in E. destruct v1 as [[]|]; congruence. }
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec.
      eapply HT_compose; try eapply genEq_spec.
      eapply ifNZ_spec_NZ with (v:=1); try omega.
      eapply HT_compose; try eapply pop_spec.
      eapply genFalse_spec.
    + intros m s [H1 H2]. subst.
      do 6 eexists. do 2 (split; eauto).
      do 2 eexists. rewrite val_eq_int. split; eauto.
Qed.

Definition orv (v1 v2 : val) : val :=
  if valToBool v1 then Vint 1 else v2.

Lemma genOr_spec : forall (Q:memory -> stack -> Prop),
  HT genOr
     (fun m s => exists v1 t1 v2 t2 s0,
                   s = (v1,t1):::(v2,t2):::s0 /\
                   forall t, Q m ((orv v1 v2,t):::s0))
     Q.
Proof.
  intros.
  eapply HT_forall_exists.  intro v1.
  eapply HT_forall_exists.  intro t1.
  eapply HT_forall_exists.  intro v2.
  eapply HT_forall_exists.  intro t2.
  eapply HT_forall_exists.  intro s0.
  intros.
  unfold genOr, orv.
  destruct (valToBool v1) eqn:E.
  - assert (v1 <> Vint 0). { intro. subst. unfold valToBool in E. congruence. }
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec.
      eapply HT_compose; try eapply genEq_spec.
      eapply ifNZ_spec_Z with (v:=0); eauto.
      eapply HT_compose; try eapply pop_spec.
      eapply genTrue_spec.
    + intros m s [H1 H2]. subst.
      do 6 eexists. do 2 (split; eauto).
      do 2 eexists. split; repeat f_equal; eauto.
      * unfold val_eq.
        destruct (equiv_dec (Vint 0) v1); congruence.
  - assert (v1 = Vint 0). { unfold valToBool in E. destruct v1 as [[]|]; congruence. }
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec.
      eapply HT_compose; try eapply genEq_spec.
      eapply ifNZ_spec_NZ with (v:=1); try omega.
      eapply nop_spec.
    + intros m s [H1 H2]. subst.
      do 6 eexists. do 2 (split; eauto).
      do 2 eexists. rewrite val_eq_int. split; eauto.
Qed.

Lemma genNot_spec :
  HTT genNot
      (fun Q m s => exists v t s0,
                      s = (Vint v, t) ::: s0 /\
                      forall t', Q m ((Vint (boolToZ (v =? 0)),t') ::: s0)).
Proof.
  intros Q.
  eapply HT_forall_exists. intros v.
  eapply HT_forall_exists. intros t.
  eapply HT_forall_exists. intros s0.
  intros.
  unfold genNot.
  cases (0 =? v) as Heq.
  - apply Z.eqb_eq in Heq. subst.
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec.
      eapply genEq_spec.
    + intros m s [H1 H2]. subst.
      do 6 eexists.
      repeat (split; eauto).
      rewrite val_eq_int. eauto.
  - eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec.
      eapply genEq_spec.
    + intros m s [H1 H2]. subst.
      do 6 eexists.
      repeat (split; eauto).
      rewrite val_eq_int. rewrite Z.eqb_sym. eauto.
Qed.

Lemma genTestEqual_spec:
  forall c1 c2 (P Q R : HProp),
    HT c2 Q (fun m s => exists v1 t1 v2 t2 s0,
                          s = (v1,t1) ::: (v2,t2) ::: s0 /\
                          forall t',
                            R m ((val_eq v1 v2, t') ::: s0)) ->
    HT c1 P Q ->
    HT (genTestEqual c1 c2) P R.
Proof.
  intros.
  unfold genTestEqual.
  eapply HT_compose; eauto.
  eapply HT_compose; eauto.
  eapply HT_strengthen_premise; try eapply genEq_spec.
  intros m s (v1 & t1 & v2 & t2 & s0 & ? & ?). subst.
  repeat eexists. eauto.
Qed.

(* ********* Specifications for loops **************** *)

(* Several different versions of the spec. *)
Lemma loopNZ_spec'': forall c I,
(forall n, (0 < n)%nat ->
  HT c
     (fun m s => exists i t s', s = CData (Vint i,t) :: s' /\ I m s /\ i = Z_of_nat n)
     (fun m s => exists i' t' s', s = CData (Vint i',t') :: s' /\ I m (CData (Vint i',t') :: s')
                                  /\ i' = Z_of_nat (pred n))) ->
(forall n, (0 < n)%nat ->
  HT (loopNZ c)
     (fun m s => exists i t s', s = CData (Vint i,t) :: s' /\ I m s /\ i = Z_of_nat n)
     (fun m s => exists s' t, s = CData (Vint 0,t) :: s' /\ I m s)).
Proof.
  intros c I P.
  unfold loopNZ, dup.
  intros n H.  generalize dependent n.
  induction n.
  intros.  inversion H.
  unfold CodeTriples.HT in *. intros.
  destruct H1 as [i [t [s' [P1 [P2 P3]]]]].

  edestruct P as [stk1 [cache1 [[i' [t' [s'' [Q1 [Q2 Q3]]]]] Q4]]].
  eapply H. eapply code_at_compose_1; eauto.
  eexists. eexists. eexists. split. eauto. eauto. eauto.
  simpl in Q3. subst stk1.
  pose proof (code_at_compose_2 _ _ _ _ H0).
  pose proof (code_at_compose_1 _ _ _ _ H1).
  pose proof (code_at_compose_2 _ _ _ _ H1).
  clear H1.
  unfold code_at in H3, H4. intuition.
  rewrite app_length in H2, H3. simpl in H2, H3.

  destruct (i' =? 0) eqn:EQ.
  - (* no loop *)
    apply Z.eqb_eq in EQ. rewrite EQ in Q3. simpl in Q3. subst i'.
    eexists. eexists. split. eexists. eexists. split. eauto. eauto.
    eapply runsToEnd_trans.
    eapply Q4. clear Q4.
    eapply runsToEnd_trans.
    eapply rte_step; eauto.
    eapply cstep_dup_p; eauto.  simpl. eauto.
    subst.
    eapply rte_step; eauto.
    eapply cstep_branchnz_p'; eauto.
    destruct (0 =? 0) eqn:E.
     eapply rte_refl; eauto.
     inv E.
    replace (n0 + Z.of_nat (length c) + 1 + 1) with (n0 + Z.of_nat (length c + 2)) by (zify; omega). subst n'. eauto.

  - (* loop *)
  assert (i' <> 0) by (eapply Z.eqb_neq;  eauto). subst.
  edestruct IHn as [stk3 [cache3 [[s''' [R1 [R2 R3]]] R4]]].
  zify; omega.
  eauto.
  eexists (Z_of_nat n).  eexists t'. eexists s''.  eauto. eauto.
  eexists.  eexists. split. eexists. eexists. split. eauto. eauto.
  subst.
  eapply runsToEnd_trans.
  eapply Q4.  clear Q4.
  repeat rewrite app_length in *. simpl in R4.
  eapply runsToEnd_trans.
  eapply rte_step. eauto.
  eapply cstep_dup_p; eauto.  simpl. eauto.
  eapply rte_step; eauto.
  eapply cstep_branchnz_p'; eauto.
  rewrite EQ. zify ; omega.
  eapply rte_refl; eauto.
Qed.

Lemma loopNZ_spec': forall c I,
(forall i, 0 < i ->
  HT c
     (fun m s => exists s' t, s = CData (Vint i,t) :: s' /\ I m s)
     (fun m s => exists i' s' t', s = CData (Vint i',t') :: s' /\ I m (CData (Vint i',t') :: s') /\
                                  i' = Z.pred i)) ->
(forall i, 0 < i ->
  HT (loopNZ c)
     (fun m s => exists s' t, s = CData (Vint i,t) :: s' /\ I m s)
     (fun m s => exists s' t, s = CData (Vint 0,t) :: s' /\ I m s)).
Proof.
  intros c I P.
  unfold loopNZ, dup.
  intros i H.  assert (0 <= i) by omega. generalize dependent H.

  set (Q := fun i => 0 < i ->
   HT (c ++ [Dup 0] ++ [BranchNZ (- Z.of_nat (length (c ++ [Dup 0])))])
     (fun (m : memory) (s : stack) => exists s' t, s = (Vint i, t) ::: s' /\ I m s)
     (fun (m : memory) (s : stack) => exists s' t, s = (Vint 0, t) ::: s' /\ I m s)).
  generalize dependent i.
  eapply (natlike_ind Q); unfold Q; clear Q.
  intros.  inversion H.
  unfold CodeTriples.HT in *. intros i E1 IH E2.
  intros.
  destruct H0 as [s' [t [P1 P2]]].

  edestruct P as [stk1 [cache1 [[i' [s'' [t' [Q1 [Q2 Q3]]]]] Q4]]].
  eauto.
  eapply code_at_compose_1; eauto.
  eexists. eexists. split. eauto. subst stk0.  eauto. eauto.
  assert (i' = i). zify; omega. rewrite H0 in Q3. try rewrite <- Q3 in *. subst i'. clear Q3.
  subst stk1.
  pose proof (code_at_compose_2 _ _ _ _ H).
  pose proof (code_at_compose_1 _ _ _ _ H0).
  pose proof (code_at_compose_2 _ _ _ _ H0).
  clear H0.
  unfold code_at in H2, H3. intuition.
  rewrite app_length in H1, H2. simpl in H1, H2.

  destruct (i =? 0) eqn:EQ.

  - (* no loop *)
  apply Z.eqb_eq in EQ. (* rewrite EQ in Q3. simpl in Q3. *) subst i.
  eexists. eexists. split. eexists. eexists. split. eauto. eauto.
  eapply runsToEnd_trans.
  eapply Q4. clear Q4.
  eapply runsToEnd_trans.
  eapply rte_step; eauto.
  eapply cstep_dup_p; eauto. simpl. eauto.
  eapply rte_step; eauto.
  eapply cstep_branchnz_p'; eauto.
  destruct (0 =?0) eqn:E.
    eauto.
    inv E.
  replace (n + Z.of_nat (length c) + 1 + 1) with (n + Z.of_nat (length c + 2)) by (zify; omega). subst n'. eauto.

  - (* loop *)
  assert (i <> 0).  eapply Z.eqb_neq;  eauto.
  edestruct IH as [stk3 [cache3 [[s''' [t'' [R1 R2]]] R3]]].
  zify; omega.
  eauto.
  exists s''.  eexists. eauto. eauto.
  eexists.  eexists. split. eexists. eexists. split. eauto. eauto.
  eapply runsToEnd_trans.
  eapply Q4.  clear Q4.
  repeat rewrite app_length in *. simpl in R3.
  eapply runsToEnd_trans.
  eapply rte_step.  eauto.
  eapply cstep_dup_p; eauto.
  simpl; eauto.
  eapply rte_step; eauto.
  eapply cstep_branchnz_p'; eauto.
  rewrite EQ. zify ; omega.
  subst.
  eapply rte_refl; auto.
Qed.

(* This is the most general version *)
Lemma loopNZ_spec: forall c I,
(forall i, 0 < i ->
  HT c
     (fun m s => exists s' t, s = CData (Vint i,t) :: s' /\ I m s)
     (fun m s => exists i' s' t, s = CData (Vint i',t) :: s' /\ I m (CData (Vint i',t) :: s') /\ 0 <= i' < i)) ->
(forall i, 0 < i ->
  HT (loopNZ c)
     (fun m s => exists s' t, s = CData (Vint i,t) :: s' /\ I m s)
     (fun m s => exists s' t, s = CData (Vint 0,t) :: s' /\ I m s)).
Proof.
  intros c I P.
  unfold loopNZ, dup.
  intros i H.  assert (0 <= i) by omega. generalize dependent H.
  set (Q := fun i => 0 < i ->
   HT (c ++ [Dup 0] ++ [BranchNZ (- Z.of_nat (length (c ++ [Dup 0])))])
     (fun (m : memory) (s : stack) => exists s' t, s = (Vint i, t) ::: s' /\ I m s)
     (fun (m : memory) (s : stack) => exists s' t, s = (Vint 0, t) ::: s' /\ I m s)).
  generalize dependent i.
  eapply (Zlt_0_ind Q); unfold Q; clear Q.
  intros i.
  unfold CodeTriples.HT in *. intros.
  destruct H3 as [s' [t' [P1 P2]]].

  edestruct P as [stk1 [cache1 [[i' [s'' [t'' [Q1 [Q2 Q3]]]]] Q4]]].
  eauto.
  eapply code_at_compose_1; eauto.
  eexists. eexists. split. eauto. subst stk0.  eauto. eauto.
  subst stk1.
  replace (@nil CEvent) with (@nil CEvent ++ @nil CEvent) by auto.
  pose proof (code_at_compose_2 _ _ _ _ H2).
  pose proof (code_at_compose_1 _ _ _ _ H3).
  pose proof (code_at_compose_2 _ _ _ _ H3).
  clear H3.
  unfold code_at in H5,H6. intuition.
  rewrite app_length in H4, H5. simpl in H4, H5.

  destruct (i =? 0) eqn:EQ.

  (* impossible *)
  apply Z.eqb_eq in EQ. subst i. inv H1.  clear EQ.

  destruct (i' =? 0) eqn: EQ.

  - (* no loop *)
  apply Z.eqb_eq in EQ. subst i'.
  eexists. eexists. split. eexists. eexists. split. eauto. eauto.
  eapply runsToEnd_trans.
  eapply Q4. clear Q4.

  eapply runsToEnd_trans.
  eapply rte_step; eauto.
  eapply cstep_dup_p; eauto.  simpl. eauto.
  subst.
  eapply rte_step; eauto.
  eapply cstep_branchnz_p'; eauto.
  destruct (0 =? 0) eqn:E.
     eapply rte_refl; eauto.
     inv E.
  replace (n + Z.of_nat (length c) + 1 + 1) with (n + Z.of_nat (length c + 2)) by (zify; omega). subst n'. eauto.

  - (* loop *)
  assert (i' <> 0).  eapply Z.eqb_neq;  eauto.
  edestruct H as [stk3 [cache3 [[s''' [t''' [R1 R2]]] R3]]].
  instantiate (1:= i').  omega.
  zify; omega.
  eauto.
  exists s''.  eauto. eauto.
  eexists.  eexists. split. eexists. eexists. split. eauto. eauto.
  eapply runsToEnd_trans.
  eapply Q4.  clear Q4.
  repeat rewrite app_length in *. simpl in R3.
  eapply runsToEnd_trans.
  eapply rte_step.  eauto.
  eapply cstep_dup_p; eauto.
  simpl; eauto.
  eapply rte_step; eauto.
  eapply cstep_branchnz_p'; eauto.
  rewrite EQ. zify ; omega.
  subst.
  eapply rte_refl; auto.

Qed.

Lemma genRepeat_spec: forall c I,
  (forall i, 0 < i ->
  HT c
     (fun m s => exists s' t, s = CData(Vint i,t)::s' /\ I m s)
     (fun m s => exists s' t, s = CData(Vint i,t)::s' /\ forall t', I m (CData(Vint (Z.pred i),t')::s'))) ->
  (forall i, 0 <= i ->
  HT (genRepeat c)
     (fun m s => exists s' t, s = CData(Vint i,t)::s' /\ I m s)
     (fun m s => exists s' t, s = CData(Vint 0,t)::s' /\ I m s)).
Proof.
  intros c I P.
  unfold genRepeat.
  intros i H.
  eapply HT_compose with (Q:= (fun m s => exists s' t, s = (Vint i,t) ::: (Vint i,t) ::: s' /\ I m ((Vint i,t):::s'))).
  eapply HT_strengthen_premise.
  eapply dup_spec.
  intros m s [s' [t' [H1 H2]]].
  eexists. split.  simpl. rewrite H1; auto.
  subst s. eexists. intuition eauto.
  (* oh gee whiz. this is unbelievably painful. *)
  set (Q := fun i m s' => exists i' t s'', s' = (Vint i,t):::s'' /\ I m s' /\ i > 0 /\ i' = i).
  set (Q0 := fun m s' => exists s'' t, s' = (Vint 0,t):::s'' /\ I m s').
  eapply HT_strengthen_premise with (fun m s => exists i' t s', s = (Vint i',t)::: s' /\
                                           (i' <> 0 -> Q i m s') /\
                                           (i' = 0 -> Q0 m s')).
  eapply ifNZ_spec with (Pt := Q i) (Pf := Q0).
  destruct (Z.eq_dec i 0). unfold CodeTriples.HT. intros. destruct H1 as [i' [t [s'' [_ [_ [CONTRA _]]]]]].  exfalso; omega.
  eapply HT_strengthen_premise.
  eapply loopNZ_spec.
  3: intros m s [i' [t [s'' [P1 [P2 P3]]]]]; eexists; intuition eauto.
  2: omega.
  intros.
  eapply HT_compose; eauto.

  { eapply HT_strengthen_premise.
    eapply HT_compose; try eapply push_spec.
    eapply add_spec.
    intros m ? (s & ? & ? & ?). subst.
    do 6 eexists. do 2 (split; eauto). reflexivity.
    do 3 eexists. split; eauto. split; try omega.
    replace (-1 + i0) with (Z.pred i0) by omega.
    eauto. }

  - eapply HT_strengthen_premise.
    + eapply nop_spec.
    + intros. destruct H0 as [s'' [t [P1 P2]]]. eexists.  intuition eauto.

  - intros m s [s' [t [P1 P2]]]. eexists. eexists. eexists.
    split; eauto.
    split.
    + intros. unfold Q. eexists. eexists. eexists. split. eauto. repeat split; eauto.  omega.
    + intros. unfold Q0. eexists. eexists. split. eauto. subst i. eauto. eauto.
Qed.

Lemma genRepeat_spec': forall c I,
  (forall i, 0 < i ->
  HT c
     (fun m s => exists s' t, s = CData(Vint i,t)::s' /\ I m s)
     (fun m s => exists s' t, s = CData(Vint i,t)::s' /\ forall t', I m (CData(Vint (Z.pred i),t')::s'))) ->
  HT (genRepeat c)
     (fun m s => exists i s' t, 0 <= i /\ s = CData(Vint i,t)::s' /\ I m s)
     (fun m s => exists s' t, s = CData(Vint 0,t)::s' /\ I m s).
Proof.
  intros c I P.

  eapply HT_forall_exists. intro i.
  eapply HT_forall_exists. intro s'.
  eapply HT_forall_exists. intro t.
  eapply HT_fold_constant_premise. intro.
  generalize t. eapply HT_exists_forall.
  generalize s'. eapply HT_exists_forall.
  eapply genRepeat_spec; eauto.
Qed.

Lemma ret_specEscape: forall raddr (Q: memory -> stack -> Prop * Outcome),
  HTEscape raddr [Ret]
    (fun m s => exists s', s = (CRet raddr false false::s') /\
                           let (prop, outcome) := Q m s' in
                           prop /\ outcome = Success)
    Q.
Proof.
  intros. cases raddr; subst.
  unfold CodeTriples.HTEscape.
  intros imem stk0 mem0 fh n CODE (s' & ? & H). subst.
  eexists s', mem0. destruct (Q mem0 s') as [prop outcome].
  intuition. subst.
  repeat eexists.
  eauto.

  (* Load an instruction *)
  subst.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_success; auto.
  eapply ruu_end; simpl; eauto.
  eapply cstep_ret_p; eauto.
  eapply cptr_done.
Qed.

Lemma jump_specEscape_Failure: forall raddr (Q: memory -> stack -> Prop * Outcome),
  HTEscape raddr [Jump]
           (fun m s => exists tag s0, (Vint (-1), tag) ::: s0 = s /\
                                      let (prop, outcome) := Q m s0 in
                                      prop /\ outcome = Failure)
           Q.
Proof.
  intros.
  unfold CodeTriples.HTEscape.
  intros imem stk0 mem0 fh n CODE (tag & s0 & ? & H). subst.
  eexists s0, mem0.
  destruct (Q mem0 s0) as [prop outcome]. destruct H; subst.
  simpl.
  repeat eexists.
  eauto.

  (* Load an instruction *)
  subst.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_fail; auto.
  eapply rte_step; eauto.
  eapply cstep_jump_p; eauto.
  simpl; eauto; omega.
Qed.

Lemma skipNZ_specEscape: forall r c1 c2 v P1 P2 Q,
  (v =  0 -> HTEscape r c1 P1 Q) ->
  (v <> 0 -> HTEscape r c2 P2 Q) ->
  HTEscape r ((skipNZ (length c1) ++ c1) ++ c2)
           (fun m s => exists s0 l, s = (Vint v, l) ::: s0 /\
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
           (fun m s => exists s0 t, s = (Vint v, t) ::: s0 /\
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

Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.

Lemma while_spec_aux :
  forall c1 c2 (P1 P2 Q R : HProp),
    HT c1 P1 (fun m s =>
                exists v t s',
                  s = (Vint v, t) ::: s' /\
                  (v = 0 /\ Q m s' \/
                   v <> 0 /\ R m s')) ->
    HT c2 Q P2 ->
    HT (c1 ++ skipNZ (length c2 + 2) ++ c2 ++
        push 1 ++ [BranchNZ (- Z.of_nat (length (c1 ++ skipNZ (length c2 + 2) ++ c2) + 1))])
       P2 R ->
    HT (c1 ++ skipNZ (length c2 + 2) ++ c2 ++
        push 1 ++ [BranchNZ (- Z.of_nat (length (c1 ++ skipNZ (length c2 + 2) ++ c2) + 1))])
       P1 R.
Proof.
  intros c1 c2 P1 P2 Q R HT1 HT2 HT3.
  intros imem stk0 mem0 fh n n' CODE PRE Hn'.
  assert (CODE1 : code_at n fh c1) by eauto using code_at_compose_1.
  exploit code_at_compose_2; eauto. intros CODE2.
  assert (CODE3 : code_at (n + Z.of_nat (length c1)) fh (skipNZ (length c2 + 2)))
    by eauto using code_at_compose_1.
  exploit HT1; eauto.
  intros (stk1' & mem1 & (v & t & stk1 & ? & COND) & RUN).
  destruct COND as [[Hv POST] | [Hv POST]]; subst stk1'.
  - generalize (skipNZ_spec_Z (length c2 + 2) Q v Hv imem
                              ((Vint v, t) ::: stk1) mem1 fh).
    intros H. exploit H; eauto. clear H.
    intros (stk2 & mem2 & POST' & RUN').
    specialize (HT2 imem).
    assert (CODE4 : code_at (n + Z.of_nat (length c1)
                               + Z.of_nat (length (skipNZ (length c2 + 2))))
                            fh c2)
      by eauto using code_at_compose_1, code_at_compose_2.
    exploit HT2; eauto.
    intros (stk3 & mem3 & POST'' & RUN'').
    exploit HT3; eauto.
    intros (stk4 & mem4 & POST''' & RUN''').
    eexists stk4, mem4. split; trivial.
    eapply runsToEnd_trans; try eapply RUN.
    eapply runsToEnd_trans; try eapply RUN'.
    eapply runsToEnd_trans; try eapply RUN''.
    eapply runsToEnd_trans; try eapply RUN'''.
    assert (CODE5 : code_at (n + Z.of_nat (length c1)
                               + Z.of_nat (length (skipNZ (length c2 + 2)))
                               + Z.of_nat (length c2))
                            fh (push 1 ++ [BranchNZ (- Z.of_nat (length (c1 ++ skipNZ (length c2 + 2) ++ c2) + 1))]))
      by eauto using code_at_compose_1, code_at_compose_2.
    simpl in CODE5. destruct CODE5 as (? & ? & _).
    eapply rte_step; try reflexivity.
    { eapply cstep_push_p; eauto. }
    eapply rte_step; try reflexivity.
    { eapply cstep_branchnz_p'; eauto. }
    simpl.
    match goal with
      | |- runsToEnd _ _
                     {| pc := (?pc1, _) |}
                     {| pc := (?pc2, _) |} =>
        cut (pc1 = pc2); try (intros E; rewrite E; eauto)
    end.
    clear.
    rewrite app_length.
    repeat rewrite Nat2Z.inj_add. simpl.
    change (Z.pos (Pos.of_succ_nat (length c2))) with (Z.of_nat (S (length c2))).
    rewrite Nat2Z.inj_succ.
    omega.
  - eexists stk1, mem1.
    split; trivial.
    eapply runsToEnd_trans; try eapply RUN.
    eapply rte_step; eauto.
    eapply cstep_branchnz_p'.
    { simpl in CODE3. intuition. eauto. }
    generalize (Z.eqb_spec v 0).
    intros REFL.
    destruct (v =? 0); inv REFL; try congruence.
    repeat rewrite app_length. simpl.
    zify. omega.
Qed.

Lemma while_spec :
  forall (I : (memory -> stack -> Prop) -> memory -> stack -> nat -> Prop)
         (Tc Tb : Trans)
         (c b : code)
         (HTTc : HTT c Tc)
         (HTTb : HTT b Tb)
         (VC : forall Q n,
                 let Pb := Tb (fun m s => exists n', n' < n /\ I Q m s n')%nat in
                 let Pc := Tc (fun m s => exists v t s0,
                                            s = (Vint v, t) ::: s0 /\
                                            (v <> 0 -> Pb m s0) /\
                                            (v = 0 -> Q m s0)) in
                 forall m s, I Q m s n -> Pc m s),
    HTT (while c b)
        (fun Q m s => exists n, I Q m s n).
Proof.
  intros.
  intros Q.
  apply HT_forall_exists. intros n.
  induction n as [n IH'] using (well_founded_ind lt_wf).
  assert (IH : HT (while c b)
                  (fun m s => exists n', n' < n /\ I Q m s n')%nat
                  Q).
  { apply HT_forall_exists. intro.
    apply HT_fold_constant_premise. auto. }
  clear IH'.
  set (Qb := (fun m s => exists n', n' < n /\ I Q m s n')%nat).
  specialize (HTTb Qb).
  set (Qc := (fun m s => exists v t s0,
                           s = (Vint v, t) ::: s0 /\
                           (v <> 0 -> Tb Qb m s0) /\
                           (v = 0 -> Q m s0))).
  specialize (HTTc Qc).
  specialize (VC Q n).
  eapply HT_strengthen_premise with (P := Tc Qc); try apply VC.
  clear VC.
  unfold while, while_body, jump_back in *.
  repeat rewrite <- app_assoc in *.
  repeat rewrite (app_assoc c genNot) in *.
  eapply while_spec_aux; eauto.
  eapply HT_compose with (Q := Qc); eauto.
  eapply HT_strengthen_premise; try eapply genNot_spec.
  clear.
  intros m s' (v & t & s & ? & H1 & H2). subst.
  do 3 eexists. split; eauto.
  intros.
  do 3 eexists. split; eauto.
  generalize (Z.eqb_spec v 0). intros REFL.
  destruct (v =? 0); inv REFL; simpl; eauto.
  intuition.
Qed.

Definition extract_offset_loop_body : code :=
            (* n :: (b,n) :: (b,off) :: s *)
  push 1 ++ (* 1 :: n :: (b,n) :: (b,off) :: s *)
  [Add]  ++ (* n+1 :: (b,n) :: (b,off) :: s *)
  swap   ++ (* (b,n) :: n+1 :: (b,off) :: s *)
  push 1 ++ (* 1 :: (b,n) :: n+1 :: (b,off) :: s *)
  [Add]  ++ (* (b,n+1) :: n+1 :: (b,off) :: s *)
  swap.     (* n+1 :: (b,n+1) :: (b,off) :: s *)

Lemma extract_offset_loop_body_spec :
  HTT extract_offset_loop_body
      (fun Q m s => exists n b off s0 t1 t2 t3,
                      s = (Vint n,t1) ::: (Vptr (b, n),t2) ::: (Vptr (b, off),t3) ::: s0 /\
                      forall t1' t2' t3',
                        Q m ((Vint (n+1),t1') ::: (Vptr (b,n+1),t2') ::: (Vptr (b,off),t3') ::: s0)).
Proof.
  unfold extract_offset_loop_body.
  eapply HTT_strengthen_premise.
  { eapply HTT_compose; try apply push_spec.
    eapply HTT_compose; try apply add_spec.
    eapply HTT_compose; try apply swap_spec.
    eapply HTT_compose; try apply push_spec.
    eapply HTT_compose; try apply add_spec.
    apply swap_spec. }
  intros Q m s (n & b & off & s0 & t1 & t2 & t3 & ? & POST).
  subst.
  Opaque Z.add.
  repeat (eexists; simpl; eauto).
  replace (1 + n) with (n + 1) by ring.
  eapply POST.
  Transparent Z.add.
Qed.

Definition extract_offset_loop : code :=
  while (           (* n :: (b,n) :: (b,off) :: s *)
         [Dup 2] ++ (* (b,off) :: n :: (b,n) :: (b,off) :: s *)
         [Dup 2] ++ (* (b,n) :: (b,off) :: n :: (b,n) :: (b,off) :: s *)
         [Eq]    ++ (* n == off :: n :: (b,n) :: (b,off) :: s *)
         genNot     (* n != off :: n :: (b,n) :: (b,off) :: s *))
        extract_offset_loop_body   (* off :: (b, off) :: (b, off) :: s *).

Definition extract_offset : code :=
             (* (b,off) :: s *)
  dup    ++  (* (b,off) :: (b,off) :: s *)
  dup    ++  (* (b,off) :: (b,off) :: (b,off) :: s *)
  sub    ++  (* (b,0) :: (b,off) :: s *)
  push 0 ++  (* 0 :: (b,0) :: (b,off) :: s *)
  extract_offset_loop ++ (* off :: (b,off) :: (b,off) :: s *)
  [Swap 2] ++ pop ++ pop.

Lemma extract_offset_spec :
  HTT extract_offset
      (fun Q m s =>
         exists p t s0,
           snd p >= 0 /\
           s = (Vptr p, t) ::: s0 /\
           forall t',
             Q m ((Vint (snd p), t') ::: s0)).
Proof.
  unfold extract_offset.
  intros.
  eapply HTT_strengthen_premise.
  { eapply HTT_compose; try eapply dup_spec.
    eapply HTT_compose; try eapply dup_spec.
    eapply HTT_compose; try eapply sub_spec.
    eapply HTT_compose; try eapply push_spec.
    eapply HTT_compose.
    { unfold extract_offset_loop.
      eapply while_spec with
        (I := fun (Q : HProp) m s n =>
                exists z b off s0 t1 t2 t3,
                  s = (Vint z, t1) ::: (Vptr (b, z), t2) ::: (Vptr (b, off), t3) ::: s0 /\
                  z = off - Z.of_nat n /\
                  forall t1' t2' t3',
                    Q m ((Vint off, t1') ::: (Vptr (b, off), t2') ::: (Vptr (b, off), t3') ::: s0)).
      - eapply HTT_compose; try eapply dup_spec.
        eapply HTT_compose; try eapply dup_spec.
        eapply HTT_compose; try eapply genEq_spec.
        eapply genNot_spec.
      - eapply extract_offset_loop_body_spec.
      - intros Q n Pb Pc m s. subst Pc Pb.
        simpl in *.
        intros (z & b & off & s' & t1 & t2 & t3 & ? & ? & POST). subst.
        eexists. split; eauto.
        eexists. split; eauto.
        do 5 eexists. split; eauto.
        unfold val_eq.
        do 3 eexists. split; eauto.
        intros t'.
        do 3 eexists. split; eauto.
        split.
        + intros H.
          match type of H with
            | context[if ?B then _ else _] => destruct B as [C|C]
          end; simpl in H; try congruence.
          assert (NZ : off - Z.of_nat n <> off) by congruence. clear C.
          do 7 eexists. split; eauto.
          intros.
          destruct n as [|n].
          { simpl in NZ. contradict NZ. ring. }
          exists n. split; try omega.
          do 7 eexists. split; eauto.
          split.
          { replace (off - Z.of_nat (S n) + 1) with (off - Z.of_nat n); eauto.
            rewrite Nat2Z.inj_succ. omega. }
          eauto.
        + intros H.
          match type of H with
            | context[if ?B then _ else _] => destruct B as [C|C]
          end; simpl in H; try congruence.
          assert (Z : off - Z.of_nat n = off) by congruence. clear C.
          assert (ZERO : Z.of_nat n = 0) by omega. clear Z.
          rewrite ZERO.
          replace (off - 0) with off by ring.
          eauto. }
    eapply HTT_compose; try eapply swap_spec.
    eapply HTT_compose; try eapply pop_spec. }
  simpl.
  intros Q m ? ([b off] & t & s & POS & ? & POST). simpl in POS. subst.
  eexists. split; eauto.
  eexists. split; eauto.
  do 4 eexists. eexists (Vptr (b, 0)). eexists.
  split; eauto.
  split.
  { simpl. rewrite equiv_dec_refl.
    repeat f_equal. ring. }
  do 8 eexists. split; eauto.
  replace 0 with (off - off) by omega.
  split; try rewrite Z2Nat.id; eauto; try omega.
  intros.
  do 4 eexists. do 3 (split; eauto).
  do 3 eexists. split; eauto.
Qed.

Lemma genSysRet_specEscape_Some: forall raddr (Q: memory -> stack -> Prop * Outcome),
  HTEscape raddr genSysRet
           (fun m s =>
              exists s0,
              s = (Vint 1, handlerTag) ::: CRet raddr false false :: s0 /\
              let (prop, outcome) := Q m s0 in
              prop /\ outcome = Success)
           Q.
Proof.
  intros.
  unfold genSysRet.
  eapply HTEscape_strengthen_premise.
  - eapply ifNZ_specEscape with (v:=1) (Pf:=fun m s => True); intros; try assumption.
    eapply ret_specEscape; try assumption.
    false.
  - subst.
    intuition. split_vc.
Qed.

Lemma genError_specEscape: forall raddr (P: memory -> stack -> Prop * Outcome),
  HTEscape raddr genError
           (fun m s => let (prop, outcome) := P m s in
                       prop /\ outcome = Failure)
           P.
Proof.
  intros.
  unfold genError.
  eapply HTEscape_strengthen_premise.
  { eapply HTEscape_compose; try eapply push_spec.
    eapply jump_specEscape_Failure. }
  simpl.
  intros m s H.
  repeat eexists; eauto.
Qed.

Lemma genSysRet_specEscape_None: forall raddr s0 m0,
 HTEscape raddr genSysRet
   (fun m s => (extends m0 m /\ s = (Vint 0, handlerTag) ::: s0))
   (fun m s => (extends m0 m /\ s = s0, Failure)).
Proof.
  intros.
  unfold genSysRet.
  eapply HTEscape_strengthen_premise.
  - eapply ifNZ_specEscape with (v := 0) (Pt := fun m s => True); intros; try assumption.
    + intuition.
    + eapply genError_specEscape.
  - intros.
    subst.
    intuition.
    jauto_set_goal; eauto.
Qed.

Lemma genSysVRet_spec :
  forall raddr (Q : memory -> stack -> Prop * Outcome),
    HTEscape raddr genSysVRet
             (fun m s =>  (exists t atom s0,
                             s = (Vint 1, t) ::: atom ::: CRet raddr true false :: s0 /\
                             let (prop, outcome) := Q m (atom ::: s0) in
                             prop /\ outcome = Success) \/
                          (exists t s0, s = (Vint 0, t) ::: s0 /\
                                        let (prop, outcome) := Q m s0 in
                                        prop /\ outcome = Failure))
             Q.
Proof.
  intros.
  unfold genSysVRet.
  destruct raddr as [pcret pcrett].
  intros code stk0 mem0 fh n code_at [H | H].
  - destruct H as (t & [resv resl] & s0 & STK & POST).
    simpl in *. destruct code_at as (H1 & H2 & H3 & H4 & H5 & H6 & _).
    eexists ((resv, resl) ::: s0), mem0. repeat eexists.
    destruct (Q mem0 ((resv, resl) ::: s0)) as [prop outcome]. destruct POST.
    simpl in *. subst. simpl. repeat (split; auto).
    eapply rte_success.
    eapply ruu_step; eauto.
    { eapply cstep_branchnz_p'; eauto. } simpl.
    replace (n + 5) with (n + 1 + 1 + 1 + 1 + 1) by ring.
    eapply ruu_end; eauto.
    eapply cstep_vret_p; eauto.
    eapply cptr_done.
  - destruct H as (t & s0 & STK & POST).
    simpl in *. destruct code_at as (H1 & H2 & H3 & H4 & H5 & H6 & _).
    eexists s0, mem0. repeat eexists.
    destruct (Q mem0 s0) as [prop outcome]. destruct POST.
    simpl in *. subst. simpl. repeat (split; auto).
    eapply rte_fail; simpl; try omega.
    eapply rte_step; try reflexivity.
    { eapply cstep_branchnz_p'; eauto. } simpl.
    eapply rte_step; try reflexivity.
    { clear H4. eapply cstep_push_p; eauto. }
    eapply rte_step; try reflexivity.
    { eapply cstep_jump_p; eauto. }
    eauto.
Qed.

End CodeSpecs.
