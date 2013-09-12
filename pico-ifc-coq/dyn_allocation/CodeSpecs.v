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

Notation cstep := (cstep cblock).
Notation runsToEscape := (runsToEscape cblock).
Notation HT := (HT cblock).
Notation HTEscape := (HTEscape cblock).

(* To stop struggling with [replace]s *)
Lemma cstep_branchnz_p' : forall m fh i s pcv pcl offv av al pc',
       read_m pcv fh = Some (BranchNZ offv) ->
       pc' = (if av =? 0 then pcv + 1 else pcv + offv) ->
       cstep (CState m fh i ((Vint av, al) ::: s) (pcv, pcl) true) Silent
             (CState m fh i s (pc',handlerTag) true).
Proof.
  intros. subst.
  constructor; auto.
Qed.

Definition imemory : Type := list Instr.
Definition stack : Type := list CStkElmt.
Definition code := list Instr.
Definition state := CS.

(* ================================================================ *)
(* Specs for concrete code *)

Ltac nil_help :=   replace (@nil CEvent) with (op_cons Silent (@nil CEvent)) by reflexivity.

(* Simplest example: the specification of a single instruction run in
privileged mode *)
Lemma add_spec: forall (z1 z2 z: val) (l1 l2: val) (m: memory) (s: stack),
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

Lemma add_spec_I: forall (z1 z2: val) (I: memory -> stack -> Prop),
 HT  [Add]
      (fun m1 s1 =>
         match s1 with
             | CData (z,l) :: CData (z',l') :: s =>
               exists zr, Memory.add z1 z2 = Some zr /\
               z = z1 /\ z' = z2 /\ I m1 s
             | _ => False
         end)
      (fun m2 s2 =>
         match s2 with
             | CData (z,l) :: s => Memory.add z1 z2 = Some z /\ I m2 s
             | _ => False
         end).
Proof.
  (* Introduce hyps *)
  intros.
  unfold CodeTriples.HT. intros.

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *.
  destruct stk0 as [| a stk0]; try solve [intuition].
  destruct a; try intuition.
  destruct a as [a l].
  destruct stk0 as [| b stk0]; try solve [intuition].
  destruct b as [[b l'] | ]; try intuition.
  split_vc.
  substs.

  split.

  Focus 2.
  eapply rte_step; eauto.
  split_vc. subst.
  eapply cstep_add_p ; eauto.
  (* Finish running *)
  simpl. eauto.
Qed.

Lemma add_spec_wp' : forall Q,
  HT [Add]
     (fun m0 s0 =>
        exists v1 t1 v2 t2 vr s,
          s0 = (v1,t1) ::: (v2,t2) ::: s /\
          add v1 v2 = Some vr /\
          Q m0 ((vr,handlerTag) ::: s))
     Q.
Proof.
  intros.
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

Lemma sub_spec_I: forall (z1 z2: val) (I: memory -> stack -> Prop),
  HT  [Sub]
      (fun m1 s1 =>
         match s1 with
             | CData (z,l) :: CData (z',l') :: s =>
               exists zr, Memory.sub z1 z2 = Some zr /\
               z = z1 /\ z' = z2 /\ I m1 s
             | _ => False
         end)
      (fun m2 s2 =>
         match s2 with
             | CData (z,l) :: s => Memory.sub z1 z2 = Some z /\ l = handlerTag /\ I m2 s
             | _ => False
         end).
Proof.
  (* Introduce hyps *)
  intros.
  unfold CodeTriples.HT. intros.

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *.
  destruct stk0 as [| a stk0]; try solve [intuition].
  destruct a; try intuition.
  destruct a as [a l].
  destruct stk0 as [| b stk0]; try solve [intuition].
  destruct b as [[b l'] | ]; try intuition.
  split_vc.
  substs.

  (* Run an instruction *)
  intuition.

  Focus 2.
  eapply rte_step; eauto.
  eapply cstep_sub_p ; eauto.

  (* Finish running *)
  simpl. auto.
Qed.

Lemma sub_spec_wp : forall Q,
  HT [Sub]
     (fun m0 s0 =>
        exists v1 t1 v2 t2 vr s,
          s0 = (v1,t1) ::: (v2,t2) ::: s /\
          Memory.sub v1 v2 = Some vr /\
          Q m0 ((vr,handlerTag) ::: s))
     Q.
Proof.
  intros.
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

Lemma dup_spec_wp: forall P n,
  HT   (Dup n :: nil)
       (fun m s => exists x, index_list n s = Some x /\ P m (x :: s))
       P.
Proof.
  intros P n.
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

Lemma swap_spec_wp: forall P n,
  HT   (Swap n :: nil)
       (fun m s => exists y s0 x s', s = y::s0 /\
                                     index_list n s = Some x /\
                                     update_list n y (x::s0) = Some s' /\
                                     P m s')
       P.
Proof.
  intros P n.
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

Lemma push_spec_I: forall v I,
  HT (push v)
     I
     (fun m s => match s with
                   | CData (Vint z,t)::tl => I m tl /\ v = z /\ t = handlerTag
                   | _ => False
                 end).
Proof.
  intros.
  intros imem mem0 stk0 c0 fh0 n Hcode HP' Hn'.
  eexists.
  eexists.

  (* Load an instruction *)
  subst.
  unfold push, code_at in *.
  intuition.
  Focus 2.
  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_push_p; eauto.

  simpl. auto.
Qed.

Lemma push_spec_wp : forall i Q,
  HT [Push i]
     (fun m s0 => Q m ((Vint i,handlerTag):::s0))
     Q.
Proof.
  intros.
  eexists.
  eexists.
  intuition eauto.

  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
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

Lemma push_cptr_spec_I: forall v I,
  HT (push_cptr v)
     I
     (fun m s => match s with
                   | CData (Vptr b addr,t)::tl => I m tl /\ b = cblock /\ addr = v /\ t = handlerTag
                   | _ => False
                 end).
Proof.
  intros.
  intros imem mem0 stk0 c0 fh0 n Hcode HP' Hn'.
  eexists.
  eexists.

  (* Load an instruction *)
  subst.
  unfold push_cptr, code_at in *.
  intuition.
  Focus 2.
  (* Run an instruction *)
  do 3 try (eapply rte_step); eauto.
  eapply cstep_push_cache_ptr_p; eauto.
  reflexivity.
  eapply cstep_push_p; eauto.
  reflexivity.
  simpl.
  replace (fh0 + 3) with (fh0 + 1 + 1 + 1) by omega.
  eapply cstep_add_p; auto.
  reflexivity.
  simpl. intuition omega.
Qed.

Lemma push_cptr_spec_wp :
  forall v Q,
    HT (push_cptr v)
       (fun m s => Q m ((Vptr cblock v, handlerTag) ::: s))
       Q.
Proof.
  intros.
  intros imem mem0 stk0 c0 fh0 n Hcode HP' Hn'.
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
  eapply cstep_add_p; auto.
  reflexivity.
  simpl. replace (v + 0) with v by omega.
  assumption.
Qed.

Lemma load_spec: forall b ofs al x, forall m0 s0,
  load b ofs m0 = Some x ->
  Mem.stamp b = Kernel ->
  HT [Load]
     (fun m s => m = m0 /\ s = CData (Vptr b ofs,al) :: s0)
     (fun m s => m = m0 /\ s = CData x :: s0).
Proof.
  intros b ofs al x m0 s0  Hmem.
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

Lemma load_spec_I: forall b a v I,
  HT [Load]
     (fun m s =>
        match s with
            | CData (Vptr b' a',al) :: tl =>
              b' = b /\ a' = a /\
              Mem.stamp b = Kernel /\
              value_on_cache b m a v /\ (* This works, even though the name is slightly misleading *)
              I m tl
            | _ => False
        end)
     (fun m s =>
        match s with
            | CData (z,t) :: tl =>
              v = z /\ I m tl
            | _ => False
        end).
Proof.
  intros b a v I. unfold CodeTriples.HT.
  intros fh stk0 mem imem pc n Hcode HP' Hn'.
  subst.
  destruct stk0 as [| hd tl]; try solve [intuition].
  destruct hd as [a' |]; try solve [intuition].
  destruct a' as [a' ].
  destruct a' as [|b' a']; intuition. subst.
  destruct H2.
  eexists. eexists.
  simpl in *.
  intuition.

  Focus 2.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_load_p; eauto.
  simpl. auto.
Qed.

Lemma load_spec_wp: forall b off t x Q,
  forall s,
  HT [Load]
     (fun m s0 => s0 = (Vptr b off,t) ::: s /\
                  Mem.stamp b = Kernel /\
                  load b off m = Some x /\
                  Q m (x ::: s))
     Q.
Proof.
  intros b off t x Q s.
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

Lemma load_spec_wp': forall Q,
  HT [Load]
     (fun m s0 => exists b off t x s,
                    s0 = (Vptr b off,t) ::: s /\
                    Mem.stamp b = Kernel /\
                    load b off m = Some x /\
                    Q m (x ::: s))
     Q.
Proof.
  intros. eapply HT_forall_exists.
  intros. eapply HT_forall_exists.
  intros. eapply HT_forall_exists.
  intros. eapply HT_forall_exists.
  intros. eapply HT_forall_exists.
  eapply load_spec_wp.
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

Lemma loadFromCache_spec: forall ofs x, forall m0 s0,
  load cblock ofs m0 = Some x ->
  HT (loadFromCache ofs)
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = CData x :: s0).
Proof.
  intros.
  eapply HT_compose.
  eapply push_cptr_spec.
  eapply load_spec.
  eauto.
  apply stamp_cblock.
Qed.

Lemma loadFromCache_spec_I: forall a v I,
  HT (loadFromCache a)
     (fun m s => value_on_cache cblock m a v /\
                 I m s)
     (fun m s =>
        match s with
            | CData (z,t) :: tl =>
              v = z /\ I m tl
            | _ => False
        end).
Proof.
  intros.
  eapply HT_compose.
  eapply push_cptr_spec_I.
  simpl.
  eapply HT_strengthen_premise.
  eapply load_spec_I with (b := cblock) (a:= a) (v:= v) (I:= I) ; eauto.
  intros.
  destruct s; try solve [intuition].
  destruct c; try solve [intuition].
  destruct a0 as [[?|b addr] t]; try solve [intuition].
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

Lemma pop_spec_I: forall v I,
  HT [Pop]
     (fun m s => match s with
                     | CData (Vint z,l) :: tl => v = z /\ I m tl
                     | _ => False
                 end)
     (fun m s => I m s).
Proof.
  unfold CodeTriples.HT.
  intros.
  subst. simpl.
  destruct stk0 as [| a tl]; try solve [intuition].
  destruct a as [z l|]; try solve [intuition].
  destruct z.
  destruct v0; try solve [intuition].
  intuition. subst.
  eexists.
  eexists.
  intuition.

  Focus 2.
  (* Load an instruction *)
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_pop_p; eauto.
  eauto.
Qed.

Lemma pop_spec_wp: forall Q,
  HT [Pop]
     (fun m s => exists v vl s0, s = (v,vl):::s0 /\ Q m s0)
     Q.
Proof.
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

Lemma nop_spec_I: forall I,  HT [Noop] I I.
Proof.
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

Lemma store_spec_I: forall b a al v vl Is (Im: memory -> Z -> Prop),
                    forall (IMperAddr: forall m a m' v,
                                         Im m a ->
                                         store b a v m = Some m' ->
                                         (forall a', a' <> a -> Im m' a')),
  HT [Store]
     (fun m s =>
        match s with
            | (Vptr b' a',zl) ::: (vz,vzl) ::: tl =>
              Mem.stamp b = Kernel /\
              b' = b /\ a' = a /\ al = zl /\
              v = vz /\ vl = vzl /\
              valid_address b a m /\
              Is tl /\ (forall a, Im m a)
            | _ => False
        end)
     (fun m s => Is s /\
                 (forall addr, addr <> a -> Im m addr) /\
                 (load b a m = Some (v,vl))).
Proof.
  unfold CodeTriples.HT.
  intros.
  subst.
  destruct stk0 ; try solve [intuition].
  destruct c as [[z1 zl] |] ; try solve [intuition].
  destruct z1; try solve [intuition].
  destruct stk0 ; try solve [intuition].
  destruct c as [[z2 zl2] |] ; try solve [intuition].
  intuition. substs.

  edestruct valid_store.
  iauto.

  eexists.
  exists x.
  intuition; subst.
  eauto.
  eapply IMperAddr; eauto.

  (* Load an instruction *)
  unfold code_at in *. intuition.

  Focus 2.
  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_store_p; eauto.
  unfold code_at in *. intuition.
  eapply load_store_new; eassumption.
Qed.

Lemma store_spec_wp' : forall Q,
       HT [Store]
         (fun (m0 : memory) (s0 : stack) =>
          exists b a al v m s,
          Mem.stamp b = Kernel /\
          s0 = (Vptr b a, al) ::: v ::: s /\ store b a v m0 = Some m /\ Q m s)
         Q.
Proof.
  intros. eapply HT_forall_exists. intro. eapply HT_forall_exists.
  intro. eapply HT_forall_exists. intro. eapply HT_forall_exists.
  intro. eapply HT_forall_exists. intro. eapply HT_forall_exists.
  intro. apply HT_fold_constant_premise. intro.
  eapply store_spec_wp. assumption.
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

Lemma alloc_spec_wp : forall Q : memory -> stack -> Prop,  (* the annotation on Q is crucial *)
  HT [Alloc]
     (fun m0 s0 => exists s t xv xl cnt,
                     s0 = (Vint cnt,t) ::: (xv, xl) ::: s /\
                     cnt >= 0 /\
                     (forall b m,
                        c_alloc Kernel cnt (xv,xl) m0 = Some (b, m) ->
                        Q m ((Vptr b 0,handlerTag):::s)))
     Q.
Proof.
  intros.
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
    eexists; intuition eauto.
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
  HT c P  (fun m s => exists t, m = m0 /\ s = (Vint v,t) ::: s0) ->
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

Lemma ite_spec_specialized_I: forall v c t f Q m0 I,
  let P := fun m s => m = m0 /\ I m s in
  HT c P
       (fun m s => match s with
                       | (Vint z,t):::tl => m = m0 /\ I m tl /\
                                            v = z
                       | _ => False
                   end) ->
  (v <> 0 -> HT t P Q) ->
  (v =  0 -> HT f P Q) ->
  HT (ite c t f) P Q.
Proof.
  introv HTc HZ HNZ.
  eapply ite_spec with (Pt := fun m s => v <> 0 /\ m = m0 /\ I m s)
                       (Pf := fun m s => v =  0 /\ m = m0 /\ I m s).
  - eapply HT_weaken_conclusion; eauto.
    go_match.
    repeat eexists; eauto.

  - eapply HT_fold_constant_premise; auto.
  - eapply HT_fold_constant_premise; auto.
Qed.

Lemma ite_spec_specialized': forall v c t f Q, forall m0 s0,
  let P := fun m s => extends m0 m /\ s = s0 in
  HT c (fun m s => extends m0 m /\ s = s0)
       (fun m s => exists t, extends m0 m /\ s = (Vint v,t) ::: s0) ->
  (v <> 0 -> HT t P Q) ->
  (v =  0 -> HT f P Q) ->
  HT (ite c t f) P Q.
Proof.
  introv HTc HZ HNZ.
  eapply ite_spec with (Pt := fun m s => v <> 0 /\ extends m0 m /\ s = s0)
                       (Pf := fun m s => v =  0 /\ extends m0 m /\ s = s0).
  - eapply HT_weaken_conclusion; eauto.
    go_match.
    split_vc.

  - eapply HT_fold_constant_premise; auto.
  - eapply HT_fold_constant_premise; auto.
Qed.

Lemma ite_spec_specialized_I': forall v c t f Q m0 I (Hext: extension_comp I),
  let P := fun m s => extends m0 m /\ I m s in
  HT c P
       (fun m s => match s with
                       | (Vint z,t):::tl => extends m0 m /\ I m tl /\
                                            v = z
                       | _ => False
                   end) ->
  (v <> 0 -> HT t P Q) ->
  (v =  0 -> HT f P Q) ->
  HT (ite c t f) P Q.
Proof.
  introv Hext HTc HZ HNZ.

  eapply ite_spec with (Pt := fun m s => v <> 0 /\ extends m0 m /\ I m s)
                       (Pf := fun m s => v =  0 /\ extends m0 m /\ I m s).
  - eapply HT_weaken_conclusion; eauto.
    go_match.
    split_vc.

  - eapply HT_fold_constant_premise; auto.
  - eapply HT_fold_constant_premise; auto.
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

Lemma some_spec_I: forall c, forall P Q,
  HT c P Q ->
  HT (some c) P
     (fun m s =>
        match s with
            | (Vint 1,t) ::: tl => Q m tl
            | _ => False
        end).
Proof.
  introv HTc.
  unfold some.
  eapply HT_compose.
  eauto.
  specialize (push_spec_I 1 Q). intros Hspec.
  eapply HT_weaken_conclusion; eauto.
  go_match.
Qed.

Definition none_spec     := push_spec''.
Definition genTrue_spec  := push_spec''.
Definition genFalse_spec := push_spec''.

Definition ZtoBool (z:Z) :=  negb (z =? 0).
Definition valToBool (v : val) :=
  match v with
    | Vint 0 => false
    | _ => true
  end.

Lemma genEq_spec: forall v1 t1 v2 t2 m0 s0,
  HT genEq
     (fun m s => m = m0 /\ s = (v1,t1):::(v2,t2):::s0)
     (fun m s => m = m0 /\ s = (val_eq v1 v2,handlerTag):::s0).
Proof.
  intros. unfold genEq.
  intros imem stk0 mem0 fh n n' CODE [? ?] Hn'. subst.
  simpl in CODE. destruct CODE as [CODE _].

  repeat eexists.

  eapply rte_step; eauto.

  eapply cstep_eq_p; eauto.
Qed.

Lemma genEq_spec_wp : forall Q : memory -> stack -> Prop,
  HT genEq
     (fun m s => exists v1 t1 v2 t2 m0 s0 ,
                   m = m0 /\ (* tedious trick again *)
                   s = (v1,t1):::(v2,t2):::s0 /\
                   Q m0 ((val_eq v1 v2,handlerTag):::s0))
     Q.
Proof.
  intros.
  eapply HT_forall_exists. intro v1.
  eapply HT_forall_exists. intro t1.
  eapply HT_forall_exists. intro v2.
  eapply HT_forall_exists. intro t2.
  eapply HT_forall_exists. intro m0.
  eapply HT_forall_exists. intro s0.
  eapply HT_consequence'.
  eapply genEq_spec; eauto.
  intros. simpl. jauto.
  intros. destruct H as [m' [s' [? [? ?]]]]. simpl in H0. destruct H0. subst.  auto.
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

Lemma genAnd_spec: forall b1 t1 b2 t2, forall m0 s0,
  HT genAnd
     (* We need [handlerTag] on [b2] because [genAnd] returns [b2] when
        [b1] is [true]. *)
     (fun m s => m = m0 /\ s = CData (Vint (boolToZ b1),t1) ::
                               CData (Vint (boolToZ b2),t2) :: s0)
     (fun m s => m = m0 /\ exists t, s = CData (Vint (boolToZ (andb b1 b2)),t) :: s0).
Proof.
  intros.
  unfold genAnd.
  destruct b1; eapply HT_strengthen_premise.
  - eapply HT_compose; [eapply push_spec_wp|].
    eapply HT_compose; [eapply genEq_spec_wp|].
    eapply ifNZ_spec_Z with (v:=0); eauto.
    apply nop_spec_wp.
  - intros m s [H1 H2]. subst.
    repeat (eexists; try split; eauto).
    rewrite val_eq_int. reflexivity.
  - eapply HT_compose; [eapply push_spec_wp|].
    eapply HT_compose; [eapply genEq_spec_wp|].
    eapply ifNZ_spec_NZ with (v:=1); try congruence.
    eapply HT_compose; [eapply pop_spec_wp|].
    eapply genFalse_spec_wp.
  - intros m s [H1 H2]. subst.
    repeat (eexists; try split; eauto).
    rewrite val_eq_int. reflexivity.
Qed.

Lemma genAnd_spec_I: forall b1 b2, forall I,
  HT genAnd
     (fun m s =>
        match s with
          | CData (Vint z1 ,t1) ::CData (Vint z2,t2) :: tl =>
            z1 = boolToZ b1 /\ z2 = boolToZ b2 /\
            I m tl
          | _ => False
        end)
     (fun m s =>
        match s with
          | CData (Vint z,t) :: tl =>
            z = boolToZ (andb b1 b2) /\
            I m tl
          | _ => False
        end).
Proof.
  intros.
  unfold genAnd.
  destruct b1; eapply HT_strengthen_premise.
  - eapply HT_compose; [eapply push_spec_wp|].
    eapply HT_compose; [eapply genEq_spec_wp|].
    eapply ifNZ_spec_Z with (v:=0); eauto.
    apply nop_spec_wp.
  - go_match.
    repeat (eexists; try split; eauto).
    + rewrite val_eq_int. reflexivity.
    + simpl. eauto.
  - eapply HT_compose; [eapply push_spec_wp|].
    eapply HT_compose; [eapply genEq_spec_wp|].
    eapply ifNZ_spec_NZ with (v:=1); try congruence.
    eapply HT_compose; [eapply pop_spec_wp|].
    eapply genFalse_spec_wp.
  - go_match.
    repeat (eexists; try split; eauto).
    rewrite val_eq_int. reflexivity.
Qed.

Definition andv (v1 v2 : val) : val :=
  if valToBool v1 then v2 else Vint 0.

Lemma genAnd_spec_general : forall v1 t1 v2 t2, forall m0 s0,
  HT genAnd
     (fun m s => m = m0 /\ s = (v1,t1):::(v2,t2):::s0)
     (fun m s => m = m0 /\ exists t, s = (andv v1 v2,t):::s0).
Proof.
  intros.
  unfold genAnd, andv.
  destruct (valToBool v1) eqn:E.
  - assert (v1 <> Vint 0). { intro. subst. unfold valToBool in E. congruence. }
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec_wp.
      eapply HT_compose; try eapply genEq_spec_wp.
      eapply ifNZ_spec_Z with (v:=0); eauto.
      apply nop_spec_wp.
    + intros m s [H1 H2]. subst.
      do 6 eexists. do 2 (split; eauto).
      do 2 eexists. split; repeat f_equal; eauto.
      unfold val_eq.
      destruct (equiv_dec (Vint 0) v1); congruence.
  - assert (v1 = Vint 0). { unfold valToBool in E. destruct v1 as [[]|]; congruence. }
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec_wp.
      eapply HT_compose; try eapply genEq_spec_wp.
      eapply ifNZ_spec_NZ with (v:=1); try omega.
      eapply HT_compose; try eapply pop_spec_wp.
      eapply genFalse_spec_wp.
    + intros m s [H1 H2]. subst.
      do 6 eexists. do 2 (split; eauto).
      do 2 eexists. rewrite val_eq_int. split; eauto.
      do 3 eexists. repeat (split; eauto).
Qed.

Lemma genAnd_spec_general_wp : forall (Q:memory -> stack -> Prop),
  HT genAnd
     (fun m s => exists v1 t1 v2 t2 s0,
                   s = (v1,t1):::(v2,t2):::s0 /\
                   forall t, Q m ((andv v1 v2,t):::s0))
     Q.
Proof.
  intros.
  eapply HT_strengthen_premise with
     (fun m s => exists v1 t1 v2 t2 s0 m0,
                   s = (v1,t1):::(v2,t2):::s0 /\ m = m0 /\
                   forall t, Q m0 ((andv v1 v2,t):::s0)).
  eapply HT_forall_exists.  intro v1.
  eapply HT_forall_exists.  intro t1.
  eapply HT_forall_exists.  intro v2.
  eapply HT_forall_exists.  intro t2.
  eapply HT_forall_exists.  intro s0.
  eapply HT_forall_exists.  intro m1.
  eapply HT_consequence'.
  eapply genAnd_spec_general.
  split_vc.
  split_vc. subst. eauto.
  split_vc.
Qed.

Lemma genOr_spec: forall b1 t1 b2 t2, forall m0 s0,
  HT genOr
     (fun m s => m = m0 /\ s = CData (Vint (boolToZ b1),t1) ::
                               CData (Vint (boolToZ b2),t2) :: s0)
     (fun m s => m = m0 /\ exists t, s = CData (Vint (boolToZ (orb b1 b2)),t) :: s0).
Proof.
  intros.
  unfold genOr.
  destruct b1; eapply HT_strengthen_premise.
  - eapply HT_compose; [eapply push_spec_wp|].
    eapply HT_compose; [eapply genEq_spec_wp|].
    eapply ifNZ_spec_Z with (v:=0); try omega.
    eapply HT_compose; try eapply pop_spec_wp.
    eapply genTrue_spec_wp.
  - intros m s [H1 H2]. subst.
    do 6 eexists. do 2 (split; eauto).
    rewrite val_eq_int. simpl.
    repeat (eexists; try split; eauto).
  - eapply HT_compose; [eapply push_spec_wp|].
    eapply HT_compose; [eapply genEq_spec_wp|].
    eapply ifNZ_spec_NZ with (v:=1); try congruence.
    eapply nop_spec_wp.
  - intros m s [H1 H2]. subst.
    repeat (eexists; try split; eauto).
    rewrite val_eq_int. reflexivity.
Qed.

Lemma genOr_spec_I: forall b1 b2, forall I,
  HT genOr
     (fun m s =>
        match s with
          | CData (Vint z1 ,t1) ::CData (Vint z2,t2) :: tl =>
            z1 = boolToZ b1 /\ z2 = boolToZ b2 /\
            I m tl
          | _ => False
        end)
     (fun m s =>
        match s with
          | CData (Vint z,t) :: tl =>
            z = boolToZ (orb b1 b2) /\
            I m tl
          | _ => False
        end).
Proof.
  intros.
  unfold genAnd.
  destruct b1; eapply HT_strengthen_premise.
  - eapply HT_compose; [eapply push_spec_wp|].
    eapply HT_compose; [eapply genEq_spec_wp|].
    eapply ifNZ_spec_Z with (v:=0); eauto.
    eapply HT_compose; [eapply pop_spec_wp|].
    eapply genTrue_spec_wp.
  - go_match.
    repeat (eexists; try split; eauto).
    + rewrite val_eq_int. reflexivity.
  - eapply HT_compose; [eapply push_spec_wp|].
    eapply HT_compose; [eapply genEq_spec_wp|].
    eapply ifNZ_spec_NZ with (v:=1); try congruence.
    eapply nop_spec_wp.
  - go_match.
    repeat (eexists; try split; eauto).
    + rewrite val_eq_int. reflexivity.
    + simpl. eauto.
Qed.

Definition orv (v1 v2 : val) : val :=
  if valToBool v1 then Vint 1 else v2.

Lemma genOr_spec_general : forall v1 t1 v2 t2, forall m0 s0,
  HT genOr
     (fun m s => m = m0 /\ s = (v1,t1):::(v2,t2):::s0)
     (fun m s => m = m0 /\ exists t, s = (orv v1 v2,t):::s0).
Proof.
  intros.
  unfold genOr, orv.
  destruct (valToBool v1) eqn:E.
  - assert (v1 <> Vint 0). { intro. subst. unfold valToBool in E. congruence. }
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec_wp.
      eapply HT_compose; try eapply genEq_spec_wp.
      eapply ifNZ_spec_Z with (v:=0); eauto.
      eapply HT_compose; try eapply pop_spec_wp.
      eapply genTrue_spec_wp.
    + intros m s [H1 H2]. subst.
      do 6 eexists. do 2 (split; eauto).
      do 2 eexists. split; repeat f_equal; eauto.
      * unfold val_eq.
        destruct (equiv_dec (Vint 0) v1); congruence.
      * repeat (eexists; try split; eauto).
  - assert (v1 = Vint 0). { unfold valToBool in E. destruct v1 as [[]|]; congruence. }
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec_wp.
      eapply HT_compose; try eapply genEq_spec_wp.
      eapply ifNZ_spec_NZ with (v:=1); try omega.
      eapply nop_spec_wp.
    + intros m s [H1 H2]. subst.
      do 6 eexists. do 2 (split; eauto).
      do 2 eexists. rewrite val_eq_int. split; eauto.
Qed.

Lemma genOr_spec_general_wp : forall (Q:memory -> stack -> Prop),
  HT genOr
     (fun m s => exists v1 t1 v2 t2 s0,
                   s = (v1,t1):::(v2,t2):::s0 /\
                   forall t, Q m ((orv v1 v2,t):::s0))
     Q.
Proof.
  intros.
  eapply HT_strengthen_premise with
     (fun m s => exists v1 t1 v2 t2 s0 m0,
                   s = (v1,t1):::(v2,t2):::s0 /\ m = m0 /\
                   forall t, Q m0 ((orv v1 v2,t):::s0)).
  eapply HT_forall_exists.  intro v1.
  eapply HT_forall_exists.  intro t1.
  eapply HT_forall_exists.  intro v2.
  eapply HT_forall_exists.  intro t2.
  eapply HT_forall_exists.  intro s0.
  eapply HT_forall_exists.  intro m1.
  eapply HT_consequence'.
  eapply genOr_spec_general.
  split_vc.
  split_vc. subst. eauto.
  split_vc.
Qed.

Lemma genNot_spec_general: forall v t, forall m0 s0,
  HT genNot
     (fun m s => m = m0 /\ s = CData (Vint v, t) :: s0)
     (fun m s => m = m0 /\
                 s = CData (Vint (boolToZ (v =? 0)),handlerTag) :: s0).
Proof.
  intros.
  unfold genNot.
  cases (0 =? v) as Heq.
  - apply Z.eqb_eq in Heq. subst.
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec_wp.
      eapply genEq_spec_wp.
    + intros m s [H1 H2]. subst.
      do 6 eexists.
      repeat (split; eauto).
      rewrite val_eq_int. reflexivity.
  - eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec_wp.
      eapply genEq_spec_wp.
    + intros m s [H1 H2]. subst.
      do 6 eexists.
      repeat (split; eauto).
      rewrite val_eq_int. rewrite Z.eqb_sym. reflexivity.
Qed.

Lemma genNot_spec_general_I: forall v, forall I,
  HT genNot
     (fun m s => match s with
                   | (Vint z, t) ::: tl =>
                     v = z /\ I m tl
                   | _ => False
                 end)
     (fun m s => match s with
                   | (Vint z,t) ::: tl =>
                     boolToZ (v =? 0) = z /\ I m tl
                   | _ => False
                 end).
Proof.
  intros.
  unfold genNot.
  cases (0 =? v) as Heq.
  - apply Z.eqb_eq in Heq. subst.
    eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec_wp.
      eapply genEq_spec_wp.
    + go_match.
      do 6 eexists.
      repeat (split; eauto).
      destruct (equiv_dec (Vint 0) (Vint 0)); congruence.
  - eapply HT_strengthen_premise.
    + eapply HT_compose; try eapply push_spec_wp.
      eapply genEq_spec_wp.
    + go_match.
      do 6 eexists.
      repeat (split; eauto).
      destruct (equiv_dec (Vint 0) (Vint n)).
      * assert (0 = n) by congruence. subst. simpl in *. congruence.
      * rewrite Z.eqb_sym. rewrite Heq. reflexivity.
Qed.

Lemma genNot_spec: forall b t, forall m0 s0,
  HT genNot
     (fun m s => m = m0 /\ s = (Vint (boolToZ b), t) ::: s0)
     (fun m s => m = m0 /\ s = (Vint (boolToZ (negb b)), handlerTag) ::: s0).
Proof.
  intros.
  eapply HT_weaken_conclusion.
  - eapply genNot_spec_general.
  - cases b; auto.
Qed.

Lemma genNot_spec_wp : forall Q : HProp,
  HT genNot
     (fun m s => exists b t s0,
                   s = (Vint (boolToZ b), t) ::: s0 /\
                   forall t', Q m ((Vint (boolToZ (negb b)),t') ::: s0))
     Q.
Proof.
  intros.
  eapply HT_forall_exists. intros b.
  eapply HT_forall_exists. intros t.
  eapply HT_forall_exists. intros s0.
  eapply HT_strengthen_premise with
    (P := fun m s => exists m0, Q m0 ((Vint (boolToZ (negb b)),handlerTag) ::: s0) /\
                                m = m0 /\
                                s = (Vint (boolToZ b), t) ::: s0).
  { eapply HT_forall_exists. intros m0.
    eapply HT_fold_constant_premise. intros H.
    eapply HT_weaken_conclusion; try eapply genNot_spec.
    simpl. intros m s [H1 H2]. subst. assumption. }
  intros m s [H1 H2]. subst.
  repeat eexists; eauto.
Qed.

Lemma genImpl_spec: forall b1 t1 b2 t2, forall m0 s0,
  HT genImpl
     (fun m s => m = m0 /\ s = CData (Vint (boolToZ b1),t1) ::
                               CData (Vint (boolToZ b2),t2) :: s0)
     (fun m s => m = m0 /\ exists t, s = CData (Vint (boolToZ (implb b1 b2)),t) :: s0).
Proof.
  intros.
  eapply HT_weaken_conclusion.
  unfold genImpl.
  eapply HT_compose.
  eapply genNot_spec.
  eapply genOr_spec.
  simpl. cases b1; cases b2; iauto.
Qed.

(*
(* NC: use [Z.eqb_eq] and [Z.eqb_neq] to relate the boolean equality
   to propositional equality. *)
Lemma genTestEqual_spec: forall c1 c2, forall v1 v2, forall m0,
  (forall s0,
     HT c1
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ exists t, s = (v1,t) ::: s0)) ->
  (forall s0,
     HT c2
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ exists t, s = (v2,t) ::: s0)) ->
  (forall s0,
     HT (genTestEqual c1 c2)
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (val_eq v2 v1,handlerTag) ::: s0)).
Proof.
  intros.
  unfold genTestEqual.
  eapply HT_compose; eauto.
  eapply HT_compose.
  { eapply HT_strengthen_premise.
    2: intros m s [? [t ?]]. subst.
  eapply HT_strengthen_premise.
  { eapply genEq_spec_wp. }
  split_vc.
Qed.
*)

Lemma genTestEqual_spec_I: forall c1 c2, forall v1 v2, forall m0,
  (forall I (Hext: extension_comp I),
     HT c1
        (fun m s => extends m0 m /\ I m s)
        (fun m s => match s with
                        | (z1,t):::tl =>
                          v1 = z1 /\ extends m0 m /\ I m tl
                        | _ => False
                    end)) ->
  (forall I (Hext: extension_comp I),
     HT c2
        (fun m s => extends m0 m /\ I m s)
        (fun m s => match s with
                      | (z2,t)::: tl =>
                        extends m0 m /\ v2 = z2 /\ I m tl
                      | _ => False
                    end)) ->
  (forall I (Hext: extension_comp I),
     HT (genTestEqual c1 c2)
        (fun m s => extends m0 m /\ I m s)
        (fun m s => match s with
                      | (z,t)::: tl =>
                        extends m0 m /\ val_eq v2 v1 = z /\
                        I m tl
                      | _ => False
                    end)).
Proof.
  intros.
  unfold genTestEqual.
  eapply HT_compose.
  eapply H; auto.
  eapply HT_compose.
  eapply HT_strengthen_premise.
  eapply H0 with
  (I:= fun m s =>  match s with
                     | (z1,t1):::tl =>
                       z1 = v1 /\
                       I m tl /\ extends m0 m
                     | _ => False
                   end).
  unfold extension_comp, extends.
  intros; intuition. go_match.
  go_match.
  eapply HT_strengthen_premise.
  { eapply genEq_spec_wp. }
  intros.
  go_match.
  split_vc.
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
  eapply cstep_dup_p.  eauto. simpl. eauto.
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
  eapply dup_spec_wp.
  intros m s [s' [t' [H1 H2]]].
  eexists. split.  simpl. rewrite H1; auto.
  subst s. eexists. intuition eauto.
  (* oh gee whiz. this is unbelievably painful. *)
  set (Q := fun i m s' => exists i' t s'', s' = (Vint i,t):::s'' /\ I m s' /\ i > 0 /\ i' = i).
  set (Q0 := fun m s' => exists s'' t, s' = (Vint 0,t):::s'' /\ I m s').
  eapply HT_strengthen_premise with (fun m s => exists i' t s', s = (Vint i',t)::: s' /\
                                           (i' <> 0 -> Q i m s') /\
                                           (i' = 0 -> Q0 m s')).
  eapply ifNZ_spec_existential with (Pt := Q i) (Pf := Q0).
  destruct (Z.eq_dec i 0). unfold CodeTriples.HT. intros. destruct H1 as [i' [t [s'' [_ [_ [CONTRA _]]]]]].  exfalso; omega.
  eapply HT_strengthen_premise.
  eapply loopNZ_spec.
  3: intros m s [i' [t [s'' [P1 [P2 P3]]]]]; eexists; intuition eauto.
  2: omega.
  intros.
  eapply HT_compose.
  apply P; auto.
  eapply HT_compose.
  eapply push_spec'.

  eapply HT_strengthen_premise.
  eapply add_spec_wp'.
  simpl. intros m s [R1 [s' [t [R2 R3]]]].
  eexists (Vint (-1)). eexists handlerTag. eexists (Vint i0). eexists t. eexists (Vint (i0 - 1)). eexists.
  repeat split.
  - destruct s. inv R1. inv R1. simpl in R2. subst s. split; eauto.
  - replace (i0 - 1) with ((-1) + i0) by omega. reflexivity.
  - eexists. eexists. eexists. split. eauto.
    split; auto; omega.
  - eapply HT_strengthen_premise.
    + eapply nop_spec_wp.
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

Definition extract_offset_body : code :=
            (* n :: (b,n) :: (b,off) :: s *)
  push 1 ++ (* 1 :: n :: (b,n) :: (b,off) :: s *)
  [Add]  ++ (* n+1 :: (b,n) :: (b,off) :: s *)
  swap   ++ (* (b,n) :: n+1 :: (b,off) :: s *)
  push 1 ++ (* 1 :: (b,n) :: n+1 :: (b,off) :: s *)
  [Add]  ++ (* (b,n+1) :: n+1 :: (b,off) :: s *)
  swap.     (* n+1 :: (b,n+1) :: (b,off) :: s *)

Lemma extract_offset_body_spec : forall Q : HProp,
  HT extract_offset_body
     (fun m s => exists n b off s0 t1 t2 t3,
                   s = (Vint n,t1) ::: (Vptr b n,t2) ::: (Vptr b off,t3) ::: s0 /\
                   forall t1' t2' t3',
                     Q m ((Vint (n+1),t1') ::: (Vptr b (n+1),t2') ::: (Vptr b off,t3') ::: s0))
     Q.
Proof.
  intros.
  unfold extract_offset_body.
  eapply HT_strengthen_premise.
  eapply HT_compose; try apply push_spec_wp.
  eapply HT_compose; try apply add_spec_wp'.
  eapply HT_compose; try apply swap_spec_wp.
  eapply HT_compose; try apply push_spec_wp.
  eapply HT_compose; try apply add_spec_wp'.
  apply swap_spec_wp.
  intros m s (n & b & off & s0 & t1 & t2 & t3 & ? & POST).
  subst.
  Opaque Z.add.
  repeat (eexists; simpl; eauto).
  replace (1 + n) with (n + 1) by ring.
  eapply POST.
  Transparent Z.add.
Qed.

Definition extract_offset_loop : code :=
             (* n :: (b,n) :: (b,off) :: s *)
  [Dup 1] ++ (* (b,n) :: n :: (b,n) :: (b,off) :: s *)
  [Dup 3] ++ (* (b,off) :: (b,n) :: n :: (b,n) :: (b,off) :: s *)
  [Eq]    ++ (* n == off :: n :: (b,n) :: (b,off) :: s *)
  [BranchNZ (Z.of_nat (length extract_offset_body + 2))] ++
  extract_offset_body ++
  push 1 ++
  [BranchNZ (- Z.of_nat (4 + length extract_offset_body))] ++

  (* off :: (b, off) :: (b, off) :: s *)
  [Swap 2] ++ pop ++ pop.

Definition extract_offset : code :=
             (* (b,off) :: s *)
  dup    ++  (* (b,off) :: (b,off) :: s *)
  dup    ++  (* (b,off) :: (b,off) :: (b,off) :: s *)
  sub    ++  (* (b,0) :: (b,off) :: s *)
  push 0 ++  (* 0 :: (b,0) :: (b,off) :: s *)
  extract_offset_loop.

End CodeSpecs.
