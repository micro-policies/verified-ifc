(* Generic tools for proving properties of (privileged) concrete machine code. *)

Require Import ZArith.
Require Import Lia.
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
   | |- ?P /\ ?Q => (split; [(eauto; try (zify; lia);fail) | split_vc])
   | _ => (eauto; try (zify; lia))
   end).

Ltac split_vc' :=
  (try subst; simpl;
   match goal with
   | H: exists X,_ |- _ => (destruct H; split_vc')
   | H: ?P /\ ?Q |- _ => (destruct H; split_vc')
   | |- exists X, _ => (eexists; split_vc')
   | |- ?P /\ ?Q => (split; [(eauto; try (zify; lia);fail) | split_vc'])
   | _ => (eauto; try (zify; lia))
   end).

Ltac run1 L := eapply rte_step; eauto; eapply L; eauto.

Section CodeSpecs.
Local Open Scope Z_scope.

Variable cblock : block.
Variable stamp_cblock : Mem.stamp cblock = Kernel.
Variable table : CSysTable.

Notation cstep := (cstep cblock table).
Notation runsToEscape := (runsToEscape cblock table).
Notation HT := (HT cblock table).
Notation HTEscape := (HTEscape cblock table).

(* To stop struggling with [replace]s *)
Lemma cstep_branchnz_p' : forall m fh i s pcv pcl offv av al pc',
       read_m pcv fh = Some (BranchNZ offv) ->
       pc' = (if av =? 0 then pcv + 1 else pcv + offv) ->
       cstep (CState m fh i ((Vint av, al) ::: s) (pcv, pcl) true) Silent
             (CState m fh i s (pc',handlerTag) true).
Proof.
  intros. subst.
  [> once (econstructor; solve [eauto]) ..].
Qed.

Definition imemory : Type := list Instr.
Definition stack : Type := list CStkElmt.
Definition code := list Instr.
Definition state := CS.

(* ================================================================ *)
(* Specs for concrete code *)

Ltac nil_help :=   replace (@nil CEvent) with (op_cons Silent (@nil CEvent)) by reflexivity.

Lemma add_spec : forall Q,
  HT [Add]
     (fun m0 s0 =>
        exists v1 t1 v2 t2 vr s,
          s0 = (v1,t1) ::: (v2,t2) ::: s /\
          add v1 v2 = Some vr /\
          Q m0 ((vr,handlerTag) ::: s))
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_add_p.
Qed.

Lemma sub_spec : forall Q,
  HT [Sub]
     (fun m0 s0 =>
        exists v1 t1 v2 t2 vr s,
          s0 = (v1,t1) ::: (v2,t2) ::: s /\
          Memory.sub v1 v2 = Some vr /\
          Q m0 ((vr,handlerTag) ::: s))
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_sub_p.
Qed.

Lemma dup_spec:
  forall n Q,
  HT [Dup n]
     (fun m s => exists x, index_list n s = Some x /\ Q m (x :: s))
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_dup_p.
Qed.

Lemma swap_spec: forall n Q,
  HT [Swap n]
     (fun m s => exists y s0 x s', s = y::s0 /\
                                   index_list n s = Some x /\
                                   update_list n y (x::s0) = Some s' /\
                                   Q m s')
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_swap_p.
Qed.

Lemma push_spec: forall v Q,
  HT [Push v]
     (fun m s => Q m (CData (Vint v,handlerTag) :: s))
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_push_p.
Qed.

Lemma PushCachePtr_spec : forall Q,
  HT [PushCachePtr]
     (fun m s =>
        Q m (CData (Vptr (cblock, 0),handlerTag) :: s))
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_push_cache_ptr_p.
Qed.


Lemma load_spec : forall Q,
  HT [Load]
     (fun m s0 => exists p t x s,
                    s0 = (Vptr p,t) ::: s /\
                    Mem.stamp (fst p) = Kernel /\
                    load p m = Some x /\
                    Q m (x ::: s))
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_load_p.
Qed.

Lemma unpack_spec : forall Q,
  HT [Unpack]
     (fun m s => exists x l s0,
                   s = (x,l):::s0 /\
                   Q m ((l,handlerTag):::(x,handlerTag):::s0))
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_unpack_p.
Qed.

Lemma pack_spec : forall Q,
  HT [Pack]
     (fun m s => exists x t l l0 s0,
                   s = (l,t):::(x,l0):::s0 /\
                   Q m ((x,l):::s0))
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_pack_p.
Qed.


Lemma pop_spec: forall Q,
  HT [Pop]
     (fun m s => exists v vl s0, s = (v,vl):::s0 /\ Q m s0)
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_pop_p.
Qed.

Lemma nop_spec: forall Q, HT [Noop] Q Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_nop_p.
Qed.

Lemma store_spec : forall Q,
  HT [Store]
     (fun (m0 : memory) (s0 : stack) =>
        exists p al v m s,
          Mem.stamp (fst p) = Kernel /\
          s0 = (Vptr p, al) ::: v ::: s /\ store p v m0 = Some m /\ Q m s)
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_store_p.
Qed.


Lemma alloc_spec : forall Q : _ -> _ -> Prop,
  HT [Alloc]
     (fun m0 s0 => exists s t xv xl cnt,
                     s0 = (Vint cnt,t) ::: (xv, xl) ::: s /\
                     cnt >= 0 /\
                     (forall b m,
                        c_alloc Kernel cnt (xv,xl) m0 = Some (b, m) ->
                        Q m ((Vptr (b, 0),handlerTag):::s)))
     Q.
Proof.
  intros. unfold CodeTriples.HT. intros.
  inv H.
  destruct H0 as (s & t & xv & xl & cnt & ? & ? & ?).
  assert (ALLOC: exists b m',
                   c_alloc Kernel cnt (xv,xl) mem0 = Some(b,m')).
  { unfold c_alloc, alloc, zreplicate.
    destruct (Z_lt_dec cnt 0); try lia.
    match goal with
      | |- context [Some ?p = Some _] => destruct p
    end.
    eauto. }
  split_vc; subst; run1 cstep_alloc_p.
Qed.

Lemma getoff_spec : forall Q : _ -> _ -> Prop,
  HT [GetOff]
     (fun m s =>
        exists p t s0,
          s = (Vptr p, t) ::: s0 /\
          forall t', Q m ((Vint (snd p), t') ::: s0))
     Q.
Proof.
  unfold CodeTriples.HT; split_vc; subst; run1 cstep_getoff_p.
Qed.

Lemma genEq_spec : forall Q,
  HT genEq
     (fun m s => exists v1 t1 v2 t2 s0 ,
                   s = (v1,t1):::(v2,t2):::s0 /\
                   Q m ((val_eq v1 v2,handlerTag):::s0))
     Q.
Proof.
  unfold genEq. unfold CodeTriples.HT; split_vc; run1 cstep_eq_p.
Qed.


Ltac apply_wp :=
  try unfold pop, nop, push, dup, swap, sub, genEq;
  try eapply add_spec;
  try eapply sub_spec;
  try eapply genEq_spec;
  try eapply dup_spec;
  try eapply swap_spec;
  try eapply push_spec;
  try eapply pop_spec;
  try eapply PushCachePtr_spec;
  try eapply alloc_spec;
  try eapply load_spec;
  try eapply store_spec;
  try eapply unpack_spec;
  try eapply pack_spec;
  try eapply getoff_spec;
  simpl.

Ltac build_vc wptac :=
  let awp := (try apply_wp; try wptac) in
  try (eapply HT_compose_flip; [(build_vc wptac; awp)| (awp; eapply HT_strengthen_premise; awp)]).


Lemma push_cptr_spec :
  forall v Q,
    HT (push_cptr v)
       (fun m s => Q m ((Vptr (cblock, v), handlerTag) ::: s))
       Q.
Proof.
  unfold push_cptr.
  intros.
  build_vc ltac:(idtac).
  split_vc.
  replace (v + 0) with v by lia. auto.
Qed.

Lemma loadFromCache_spec: forall ofs (Q : _ -> _ -> Prop),
  HT (loadFromCache ofs)
     (fun m s =>
        exists v,
          value_on_cache cblock m ofs v /\
          forall t, Q m (CData (v, t) :: s))
     Q.
Proof.
  intros.
  unfold loadFromCache.
  build_vc ltac:(try eapply push_cptr_spec).
  split_vc'.
  intros m s (? & [] & POST).
  split_vc.
Qed.

Lemma storeAt_spec: forall a Q,
  HT (storeAt a)
     (fun m0 s0 => exists vl s m,
                     s0 = vl ::: s /\
                     store (cblock, a) vl m0 = Some m /\
                     Q m s)
     Q.
Proof.
  intros.
  unfold storeAt.
  build_vc ltac:(try eapply push_cptr_spec).
  split_vc; subst.
  intuition; eauto. (* split_vc can't quite manage the order *)
Qed.

Lemma skipNZ_continuation_spec_NZ: forall c P v,
  v <> 0 ->
  HT   (skipNZ (length c) ++ c)
       (fun m s => (exists s' l, s = CData (Vint v,l) :: s'
                                 /\ P m s'))
       P.
Proof.
  unfold CodeTriples.HT; split_vc.

  (* massage to match the rule we want to run *)
  match goal with
    | |- context[n + ?z] =>
      replace (n + z) with (if v =? 0 then n + 1 else n + z)
  end.
  run1 cstep_branchnz_p.
  rewrite <- Z.eqb_neq in H. rewrite H. auto.
Qed.

Lemma skipNZ_spec_Z: forall n P v,
  v = 0 ->
  HT   (skipNZ n)
       (fun m s => (exists s' l, s = CData (Vint v,l) :: s'
                                 /\ P m s'))
       P.
Proof.
  unfold CodeTriples.HT; split_vc; run1 cstep_branchnz_p.
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
    eapply skipNZ_continuation_spec_NZ with (v:= 1); lia. }
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
  intros; lia.
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
  forall c P Q,
    HT c P (fun m s => Q m ((Vint 1,handlerTag) ::: s)) ->
    HT (some c) P Q.
Proof.
  intros.
  unfold some.
  eapply HT_compose; eauto.
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
    + split_vc.  subst. split_vc. split; eauto.
      unfold val_eq. destruct (equiv_dec (Vint 0) v1).  congruence. eauto.
  - assert (v1 = Vint 0). { unfold valToBool in E. destruct v1 as [[]|]; congruence. }
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec.
      eapply HT_compose; try eapply genEq_spec.
      eapply ifNZ_spec_NZ with (v:=1); try lia.
      eapply HT_compose; try eapply pop_spec.
      eapply genFalse_spec.
    + split_vc. subst. rewrite val_eq_int.
      split; eauto. split_vc.
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
    + split_vc. subst. split_vc. split; eauto.
      unfold val_eq. destruct (equiv_dec (Vint 0) v1).  congruence. eauto.
  - assert (v1 = Vint 0). { unfold valToBool in E. destruct v1 as [[]|]; congruence. }
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec.
      eapply HT_compose; try eapply genEq_spec.
      eapply ifNZ_spec_NZ with (v:=1); try lia.
      eapply nop_spec.
    + split_vc. subst. rewrite val_eq_int. split; eauto.
Qed.

Lemma genNot_spec : forall Q : _ -> _ -> Prop,
  HT genNot
     (fun m s => exists v t s0,
                   s = (Vint v, t) ::: s0 /\
                   forall t', Q m ((Vint (boolToZ (v =? 0)),t') ::: s0))
     Q.
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
    + split_vc. subst. split_vc. rewrite val_eq_int. simpl. auto.
  - eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec.
      eapply genEq_spec.
    + split_vc. subst. split_vc. rewrite val_eq_int. rewrite Z.eqb_sym. eauto.
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

Lemma genLoop_spec: forall c I,
(forall i, 0 < i ->
  HT c
     (fun m s => exists s' t, s = CData (Vint i,t) :: s' /\ I m s)
     (fun m s => exists i' s' t, s = CData (Vint i',t) :: s' /\ I m (CData (Vint i',t) :: s') /\ 0 <= i' < i)) ->
HT (genLoop c)
     (fun m s => exists i, 0 < i /\ exists s' t, s = CData (Vint i,t) :: s' /\ I m s)
     (fun m s => exists s' t, s = CData (Vint 0,t) :: s' /\ I m s).
Proof.
  intros c I P.
  eapply HT_forall_exists. intros i.
  eapply HT_fold_constant_premise. intros H.
  unfold genLoop, dup.
  assert (0 <= i) by lia. generalize dependent H.
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
  replace (n + Z.of_nat (length c) + 1 + 1) with (n + Z.of_nat (length c + 2)) by (zify; lia). subst n'. eauto.

  - (* loop *)
  assert (i' <> 0).  eapply Z.eqb_neq;  eauto.
  edestruct H as [stk3 [cache3 [[s''' [t''' [R1 R2]]] R3]]].
  instantiate (1:= i').  lia.
  zify; lia.
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
  rewrite EQ. zify ; lia.
  subst.
  eapply rte_refl; auto.

Qed.

Lemma genFor_spec :
  forall I c (Q : HProp)
         (HTc : forall i,
                  i > 0 ->
                  exists Pc,
                    HT c Pc
                       (fun m s => exists t s', s = (Vint i, t) ::: s' /\ I Q m s' (Z.pred i)) /\
                    forall m s t, I Q m s i -> Pc m ((Vint i,t):::s))
         (VC : forall m s t, I Q m s 0 -> Q m ((Vint 0,t):::s)),
    HT (genFor c)
       (fun m s => exists i t s',
                     s = (Vint i,t) ::: s' /\
                     i >= 0 /\
                     I Q m s' i)
       Q.
Proof.
  intros.
  unfold genFor.
  eapply HT_strengthen_premise.
  { eapply HT_compose; try eapply dup_spec.
    eapply ifNZ_spec; try eapply nop_spec.
    eapply HT_weaken_conclusion; try eapply genLoop_spec
                                     with (I := fun m s =>
                                                  exists i ti s',
                                                    s = (Vint i, ti) ::: s' /\
                                                    I Q m s' i).
    { intros.
      assert (POS : i > 0) by lia.
      specialize (HTc i POS). clear POS.
      destruct HTc as (Pc & HTc & POST).
      eapply HT_strengthen_premise.
      { unfold push.
        eapply HT_compose; try eapply HTc.
        eapply HT_strengthen_premise.
        { eapply HT_compose; try eapply push_spec.
          eapply add_spec. }
        intros m s (? & s' & ? & INV). subst.
        do 6 eexists. split; eauto.
        split; [reflexivity|].
        replace (-1 + i) with (Z.pred i) by lia.
        do 3 eexists. split; eauto.
        split; eauto.
        lia. }
      intros m s (s' & t & ? & i' & ? & s'' & ? & ?). subst.
      assert (i' = i) by congruence.
      assert (s'' = s') by congruence. subst. eauto. }
    intros m s (s' & t & ? & i & ? & s'' & ? & ?).
    assert (i = 0) by congruence.
    assert (s'' = s') by congruence. subst. eauto. }

  intros m s (i & t & s' & ? & ? & ?). subst. simpl.
  eexists. split; eauto.
  do 3 eexists. split; eauto. split.
  - intros. eexists. split; [|do 2 eexists; split; eauto]. lia.
  - intros. subst. eauto.
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
  simpl; eauto; lia.
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
    eapply rte_fail; simpl; try lia.
    eapply rte_step; try reflexivity.
    { eapply cstep_branchnz_p'; eauto. } simpl.
    eapply rte_step; try reflexivity.
    { clear H4. eapply cstep_push_p; eauto. }
    eapply rte_step; try reflexivity.
    { eapply cstep_jump_p; eauto. }
    eauto.
Qed.

End CodeSpecs.
