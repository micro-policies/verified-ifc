Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import LibTactics.
Require Import Utils.

Require Import Instr.
Require Import AbstractCommon.
Require Import Concrete.
Require Import CodeTriples.
Require Import CodeSpecs.
Require Import Arrays.
Require Import ConcreteMachine.
Require Import Memory.
Require Import Lattices.
Require Import RefinementAQA.
Require Import RefinementQAC.
Require Import SOPCLattice.
Require Import NIAbstractMachine.

Section SOPSysCalls.

Variable cblock : block privilege.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.
Variable faultHandler : list Instr.

Definition joinPASysCall : ASysCall Zset.t := {|
  asi_arity := 2%nat;
  asi_sem S stk :=
    match stk with
      | (v2,l2) :: (Vint i,l1) :: nil =>
        Some (v2, Zset.add i (Zset.union l1 l2))
      | _ => None
    end
|}.

Definition SOPASysTable : ASysTable Zset.t :=
  fun id =>
    match id with
      | 0%nat => Some joinPASysCall
      | _ => None
    end.

Definition isPointer (v : val privilege) : bool :=
  match v with
    | Vint _ => false
    | Vptr _ _ => true
  end.

Definition genIsPointer :=
     [Dup 0]
  ++ [Sub]
  ++ [Push 0]
  ++ [Eq]
  ++ CodeGen.genNot.

Lemma sub_diag_isPointer :
  forall v,
  exists v',
    sub v v = Some v' /\
    val_eq (Vint 0) v' = boolToVal (negb (isPointer v)).
Proof.
  intros v.
  unfold val_eq.
  destruct v as [i|b off].
  - eexists (Vint 0).
    simpl.
    replace (i - i)%Z with 0%Z by omega.
    split; eauto.
    destruct (EquivDec.equiv_dec (Vint 0) (Vint 0)); try congruence.
    reflexivity.
  - eexists (Vptr b 0).
    simpl.
    destruct (EquivDec.equiv_dec b b); try congruence.
    replace (off - off)%Z with 0%Z by omega.
    split; eauto.
    destruct (EquivDec.equiv_dec (Vint 0) (Vptr b 0)); try congruence.
    reflexivity.
Qed.

Lemma genIsPointer_spec :
  forall ctable (Q : HProp),
    HT cblock ctable genIsPointer
       (fun m s =>
          exists v t s0,
            s = (v, t) ::: s0 /\
            forall t',
              Q m ((boolToVal (isPointer v), t') ::: s0))
       Q.
Proof.
  intros.
  unfold genIsPointer.
  eapply HT_strengthen_premise.
  { eapply HT_compose; try eapply dup_spec.
    eapply HT_compose; try eapply sub_spec.
    eapply HT_compose; try eapply push_spec.
    eapply HT_compose; try eapply genEq_spec_wp; eauto.
    eapply genNot_spec_wp; eauto. }
  intros m s (v & t & s0 & ? & POST). subst. simpl.
  destruct (sub_diag_isPointer v) as (v' & E1 & E2).
  eexists. split; eauto.
  do 6 eexists. do 2 (split; eauto); simpl; eauto.
  do 6 eexists. do 2 (split; eauto).
  rewrite E2. unfold boolToVal.
  do 3 eexists. split; eauto.
  intros. rewrite Bool.negb_involutive. eauto.
Qed.

Definition joinPbody :=      (* a p *)
     [Unpack]                (* at ax p *)
  ++ [Swap 2]                (* p ax at *)
  ++ [Dup 0]                 (* p p ax at *)
  ++ genIsPointer            (* b p ax at *)
  ++ CodeGen.ifNZ
     ([Pop] ++ [Pop] ++ [Pop] ++ [Push 0])
     ([Unpack]               (* pt px ax at *)
      ++ [Swap 1]            (* px pt ax at *)
      ++ [Swap 3]            (* at pt ax px *)
      ++ concat_arrays       (* apt ax px *)
      ++ [Swap 1]            (* ax apt px *)
      ++ [Swap 2]            (* px apt ax *)
      ++ [Swap 1]            (* apt px ax *)
      ++ extend_array        (* at' ax *)
      ++ [Pack]              (* a' *)
      ++ [Push 1])
.

Definition joinPCSysCallImpl := (2%nat, joinPbody).

Definition SOPCSysTable := [joinPCSysCallImpl].

Hint Resolve extends_refl.
Hint Resolve extends_trans.
Hint Resolve extends_valid_address.

Ltac apply_wp :=
  (*try unfold pop, nop, push, dup, swap;*)
  match goal with
  | |- HT _ _ [Store] _ _ => eapply store_spec_wp'
  | |- HT _ _ [Add] _ _  => eapply add_spec
  | |- HT _ _ [Dup ?N] _ _ => eapply dup_spec
  | |- HT _ _ [Swap ?N] _ _ => eapply swap_spec
  | |- HT _ _ [Load] _ _ => eapply load_spec
  | |- HT _ _ [Push ?N] _ _ => eapply push_spec
  | |- HT _ _ [Pop] _ _ => eapply pop_spec_wp
  end;
  simpl.

Ltac build_vc wptac :=
  let awp := (try apply_wp; try wptac) in
  try (eapply HT_compose_flip; [(build_vc wptac; awp)| (awp; eapply HT_strengthen_premise; awp)]).

Lemma sop_syscall_impls_correct :
  ctable_impl_correct (CLatt := SOPClatt cblock) cblock SOPASysTable SOPCSysTable faultHandler.
Proof.
  intros [|[|?]] csc FETCH;
  simpl in FETCH; inv FETCH.
  exists joinPASysCall.
  split; eauto.
  split; eauto.
  intros S Q.
  unfold joinPbody.
  eapply HT_strengthen_premise.
  { eapply HT_compose; try eapply unpack_spec_wp.
    eapply HT_compose; try eapply swap_spec.
    eapply HT_compose; try eapply dup_spec.
    eapply HT_compose; try eapply genIsPointer_spec.
    eapply ifNZ_spec_existential.
    - eapply HT_compose; try eapply pop_spec_wp.
      eapply HT_compose; try eapply pop_spec_wp.
      eapply HT_compose; try eapply pop_spec_wp.
      eapply push_spec.
    - eapply HT_compose; try eapply unpack_spec_wp.
      eapply HT_compose; try eapply swap_spec.
      eapply HT_compose; try eapply swap_spec.
      eapply HT_compose; try eapply concat_arrays_spec_wp; eauto.
      eapply HT_compose; try eapply swap_spec.
      eapply HT_compose; try eapply swap_spec.
      eapply HT_compose; try eapply swap_spec.
      eapply HT_compose; try eapply extend_array_spec_wp; eauto.
      eapply HT_compose; try eapply pack_spec_wp; eauto.
      eapply push_spec. }
  intros m s (mi & aargs & cargs & s0 & ? & LEN & MEM & MATCH & SUCC & FAIL). subst.
  destruct cargs as [|[xv1 xt1] [|[xv2 xt2] [|? ?]]]; inv LEN. simpl.
  repeat match goal with
           | H : Forall2 _ _ _ |- _ => inv H
           | H : match_atoms _ _ _ _ _ _ _ _ _ |- _ => inv H
           | H : match_tags _ _ _ |- _ => inv H
           | H : exists _, _ |- _ => inv H
           | H : _ /\ _ |- _ => inv H
         end.
  unfold boolToVal.
  repeat match goal with
           | |- exists _, _ => eexists
           | |- _ /\ _ => split; eauto
           | |- forall _, _ => intro
           | H : context[CodeGen.boolToZ (isPointer ?v) = _] |- _ =>
             destruct v; simpl in *; try congruence; clear H
           | H : match_vals _ _ _ _ (Vptr _ _) |- _ => inv H
           | H : match_vals _ _ _ _ (Vint _) |- _ => inv H
         end; eauto.
  eapply SUCC.
  - intros b fr USER DEF. eauto.
  - intros b fr KERNEL DEF. eauto.
  - simpl. reflexivity.
  - constructor; eauto.
    eexists. eexists.
    repeat match goal with
             | |- _ /\ _ => split
             | |- Vptr _ _ = Vptr _ _ => reflexivity
           end; eauto.
    + intro. subst.
      destruct MEM as [? MEM].
      match goal with
        | H : extends _ _ |- _ => apply H in MEM
      end. congruence.
    + match goal with
        | H : memarr _ _ ((map Vint ?l1 ++ map Vint ?l2) ++ [Vint ?p]) |- _ =>
          let H' := fresh "H'" in
          assert (H' : [Vint p] = (map (Vint (S := privilege)) [p])) by reflexivity;
          rewrite H' in H; clear H'
      end.
      repeat rewrite <- map_app in *. eauto.
    + intros p.
      rewrite Zset.In_add. rewrite Zset.In_union.
      rewrite in_app_iff. rewrite in_app_iff.
      repeat match goal with
               | H : context[In] |- _ => generalize H; clear H
               | H : _ |- _ => clear H
             end.
      firstorder.
Qed.

Lemma Zset_add_incl_false :
  forall p s1 s2,
    Zset.incl s1 s2 = false ->
    Zset.incl (Zset.add p s1) s2 = false.
Proof.
  intros.
  destruct (Zset.incl (Zset.add p s1) s2) eqn:E; trivial.
  rewrite Zset_incl_add in E. intuition. congruence.
Qed.

Lemma Zset_union_l_incl_false :
  forall s1 s2 s3,
    Zset.incl s1 s3 = false ->
    Zset.incl (Zset.union s1 s2) s3 = false.
Proof.
  intros.
  destruct (Zset.incl (Zset.union s1 s2) s3) eqn:E; trivial.
  rewrite Zset_incl_union in E. intuition. congruence.
Qed.

Lemma Zset_union_r_incl_false :
  forall s1 s2 s3,
    Zset.incl s2 s3 = false ->
    Zset.incl (Zset.union s1 s2) s3 = false.
Proof.
  intros.
  destruct (Zset.incl (Zset.union s1 s2) s3) eqn:E; trivial.
  rewrite Zset_incl_union in E. intuition. congruence.
Qed.

Lemma sop_asystable_lowstep : forall l, syscall_lowstep l SOPASysTable.
Proof.
  intros l id acs EQ args1 args2 res1 res2 EQUIV RES1 RES2.
  destruct id as [|[|[|?]]]; inv EQ.
  destruct args1 as [| [v12 l12] [| [[p1|? ?] l1] [|? ?]]]; inv RES1.
  destruct args2 as [| [v22 l22] [| [[p2|? ?] l2] [|? ?]]]; inv RES2.
  simpl in *.
  repeat match goal with
           | H : low_equiv_list _ (_ :: _) _ |- _ => inv H
           | H : low_equiv_stkelt _ _ _ |- _ => inv H
           | H : low_equiv_atom _ _ _ |- _ => inv H
         end; try reflexivity; constructor; simpl in *;
  eauto using Zset_add_incl_false, Zset_union_l_incl_false, Zset_union_r_incl_false.
Qed.

Lemma sop_asystable_inv : systable_inv SOPASysTable.
Proof.
  intros id args asc res EQ INV RES.
  destruct id as [|[|[|?]]]; inv EQ.
  destruct args as [| [v12 l12] [| [[p1|? ?] l1] [|? ?]]]; inv RES.
  destruct v12 as [i|b off]; simpl; trivial.
  assert (H := INV _ (or_introl eq_refl)). simpl in H.
  rewrite Zset_incl_spec in *.
  intros p IN. rewrite Zset.In_add. right.
  rewrite Zset.In_union. eauto.
Qed.

Lemma sop_asystable_parametric : parametric_asystable SOPASysTable.
Proof.
  intros [|[|[|?]]]; simpl; constructor.
  constructor.
  intros.
  destruct args1 as [|[v11 l11] [|[[p1|? ?] l12] [|? ?]]];
  repeat match goal with
           | H : Forall2 _ (_ :: _) _ |- _ => inv H
           | H : Forall2 _ [] _ |- _ => inv H
           | H : match_atoms _ _ _ _ _ _ _ _ _ |- _ => inv H
           | H : match_vals _ _ _ _ _ |- _ => inv H
           | H : RefinementAQA.match_tags _ _ _ |- _ => inv H
         end; repeat constructor; eauto.
Qed.

End SOPSysCalls.
