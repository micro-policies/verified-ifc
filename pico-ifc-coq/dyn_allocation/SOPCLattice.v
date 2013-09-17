Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import LibTactics.
Require Import Utils.

Require Import Instr.
Require Import Lattices.
Require Import Concrete.
Require Import CodeGen.
Require Import CodeTriples.
Require Import CodeSpecs.
Require Import Arrays.
Require Import Memory.
Require Import CLattices.

Local Open Scope Z_scope.

Section SOP.

Variable cblock : block privilege.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.

Definition labToVal (l: Zset.t) (t: val privilege) (m: memory (val privilege) privilege) : Prop :=
  exists c b,
    b <> cblock /\
    Mem.stamp b = Kernel /\
    t = Vptr b 0 /\
    memarr m b (map Vint c) /\
    (forall a, In a c <-> Zset.In a l).

Lemma mem_eq_except_cache_memseq :
  forall m m' b z vs
         (NCACHE : b <> cblock)
         (KERNEL : Mem.stamp b = Kernel)
         (EQ : mem_eq_except_cache cblock m m')
         (SEQ : memseq m b z vs),
    memseq m' b z vs.
Proof.
  intros.
  destruct EQ as [H1 H2].

  gdep z.
  induction vs as [|v vs IH]; intros; try solve [constructor].
  inv SEQ; econstructor; eauto.
  unfold load in *.
  destruct (Mem.get_frame m b) as [fr|] eqn:E; try congruence.
  apply H2 in E; eauto.
  rewrite E.
  eassumption.
Qed.

Lemma labToVal_cache_SOP :
  forall l v m m'
         (LAB : labToVal l v m)
         (EQ : mem_eq_except_cache cblock m m'),
    labToVal l v m'.
Proof.
  intros.
  unfold labToVal in *.
  destruct LAB as (c & b & NEQ & KERNEL & ? & ARR & IN). subst.
  eexists c, b.
  repeat (split; eauto).
  destruct ARR.
  econstructor; eauto using mem_eq_except_cache_memseq.
  unfold load in *.
  destruct (Mem.get_frame m b) as [fr|] eqn:FRAME; try congruence.
  destruct EQ as [_ EQ].
  eapply EQ in FRAME; eauto.
  rewrite FRAME. eassumption.
Qed.

Lemma memseq_extension_comp : forall m1 m2 l z off,
  memseq m1 z off l ->
  extends m1 m2 ->
  memseq m2 z off l.
Proof.
  intros m1 m2 l z off SEQ EXT.
  gdep off.
  induction l ; intros.
  constructor.
  inv SEQ.
  econstructor; eauto using extends_load.
Qed.

Lemma labToVal_extension_comp_SOP :
  forall m1 m2 l v,
    labToVal l v m1 -> extends m1 m2 -> mem_def_on_cache cblock m1 -> labToVal l v m2.
Proof.
  unfold labToVal.
  intros m1 m2 l v (c & b & NEQ & KERNEL & ? & ARR & IN) EXT DEF. subst.
  eexists c, b. repeat (split; eauto).
  destruct ARR.
  econstructor; eauto using extends_load, memseq_extension_comp.
Qed.

(* MOVE *)
Fixpoint take {T} (n : nat) (l : list T) : list T :=
  match n with
    | O => []
    | S n' =>
      match l with
        | [] => []
        | x :: l' => x :: take n' l'
      end
  end.

Definition add_principal_to_lab (ps : Zset.t) (v : val privilege) : Zset.t :=
  match v with
    | Vint p => Zset.add p ps
    | _ => ps
  end.

Definition valToLab (v : val privilege) (m: memory (val privilege) privilege) : Zset.t :=
  match v with
    | Vint _ => Zset.empty
    | Vptr b _ =>
      match Mem.get_frame m b with
        | Some ((Vint len, _) :: ps) =>
          fold_left add_principal_to_lab (map fst (take (Z.to_nat len) ps)) Zset.empty
        | _ => Zset.empty
      end
  end.

Definition genFlows : list Instr := subset_arrays.

Definition genBot : list Instr := push 0 ++ alloc_array.
Definition genJoin : list Instr := concat_arrays.

Global Instance SOPClatt : ConcreteLattice Zset.t :=
{ labToVal := labToVal
; valToLab := valToLab
; genBot := genBot
; genJoin:= genJoin
; genFlows:= genFlows
}.

Lemma memseq_incl : forall m l1 l2 b off,
 memseq m b off l1 ->
 length l1 = length l2 ->
 memseq m b off l2 -> incl l1 l2.
Proof.
  induction l1 ; intros.
  - inv H. inv H1. unfold incl. auto. inv H0.
  - inv H. destruct l2. inv H0.  inv H0.
    unfold incl. intros. inv H.
    inv H1. allinv'. constructor. auto.
    right.
    eapply IHl1; eauto.
    inv H1; eauto.
Qed.

Lemma memseq_get_frame :
  forall m b off vs fr
         (POS : off >= 0)
         (FRAME : Mem.get_frame m b = Some fr)
         (SEQ : memseq m b off vs),
    vs = map fst (take (length vs) (dropZ off fr)).
Proof.
  intros.
  induction SEQ as [off|off v t vs LOAD SEQ IH]; intros; eauto.
  unfold load in LOAD.
  rewrite FRAME in LOAD.
  assert (H : dropZ off fr = (v, t) :: dropZ (off + 1) fr).
  { clear - LOAD POS.
    unfold read_m, dropZ in *.
    destruct (off <? 0); try congruence.
    destruct (off + 1 <? 0) eqn:LT.
    - rewrite Z.ltb_lt in LT. omega.
    - rewrite Z2Nat.inj_add; try omega.
      gdep (Z.to_nat off). clear.
      intros off LOAD.
      change (off + Z.to_nat 1)%nat with (off + 1)%nat.
      rewrite plus_comm.
      gdep off.
      induction fr as [|v' fr IH]; intros [|off] H; simpl in *; eauto; try congruence.
      inv H. reflexivity. }
  rewrite H.
  simpl.
  f_equal.
  apply IH.
  omega.
Qed.

Lemma labToVal_inj_SOP : forall l1 l2 t m, labToVal l1 t m -> labToVal l2 t m -> l1 = l2.
Proof.
  unfold labToVal.
  intros l1 l2 t m
         (c1 & b & NEQ1 & KERNEL1 & E1 & ARR1 & EQ1)
         (c2 & b' & _ & _ & E2 & ARR2 & EQ2).
  assert (b' = b) by congruence. subst. clear E2.
  destruct ARR1 as [? t1 LOAD1 SEQ1 ?].
  destruct ARR2 as [? t2 LOAD2 SEQ2 ?]. subst.
  assert (LENGTHS : Z.of_nat (length (map Vint c1 : list (val privilege))) =
                    Z.of_nat (length (map Vint c2 : list (val privilege)))) by congruence.
  clear LOAD1 LOAD2.
  rewrite Nat2Z.inj_iff in LENGTHS.

  eapply Zset.antisym; eapply Zset.incl_spec.

  - assert (INCL := memseq_incl _ _ _ _ _ SEQ1 LENGTHS SEQ2).
    unfold incl. intros.
    unfold Zset.In in *.
    rewrite <- EQ2. rewrite <- EQ1 in H.
    eapply in_map in H. apply INCL in H.
    rewrite in_map_iff in H. destruct H as (? & ? & ?). congruence.

  - assert (INCL := memseq_incl _ _ _ _ _ SEQ2 (eq_sym LENGTHS) SEQ1).
    unfold incl. intros.
    unfold Zset.In in *.
    rewrite <- EQ1. rewrite <- EQ2 in H.
    eapply in_map in H. apply INCL in H.
    rewrite in_map_iff in H. destruct H as (? & ? & ?). congruence.
Qed.

Lemma Zset_union_empty : forall S, Zset.union S Zset.empty = S.
Proof.
  intros.
  apply Zset.antisym;  eapply Zset.incl_spec.
  - intros x Hin.
    eapply Zset.In_union in Hin.
    inv Hin; eauto.
    unfold Zset.In in H. rewrite Zset.elements_empty in H. inv H.
  - intros x Hin.
    eapply Zset.In_union.
    left; eauto.
Qed.

Lemma Zset_incl_spec : forall s1 s2, Zset.incl s1 s2 = true <->
                                     (forall p, Zset.In p s1 -> Zset.In p s2).
Proof.
  intros.
  split; rewrite Zset.incl_spec in *; unfold Zset.In; intros; eauto.
Qed.

Lemma Zset_incl_empty : forall s, Zset.incl Zset.empty s = true.
Proof.
  intros.
  rewrite Zset.incl_spec, Zset.elements_empty.
  intros z H. inv H.
Qed.

Lemma Zset_incl_trans : forall s1 s2 s3, Zset.incl s1 s2 = true ->
                                         Zset.incl s2 s3 = true ->
                                         Zset.incl s1 s3 = true.
Proof.
  intros.
  rewrite Zset.incl_spec in *.
  eauto using incl_tran.
Qed.

Lemma Zset_incl_union : forall s1 s2 s3, Zset.incl (Zset.union s1 s2) s3 = true <->
                                         (Zset.incl s1 s3 = true) /\ (Zset.incl s2 s3 = true).
Proof.
  intros.
  split; intros; repeat rewrite Zset_incl_spec in *.
  - split;
    intros p IN;
    apply H;
    rewrite Zset.In_union; eauto.
  - destruct H as [H1 H2].
    intros p IN.
    rewrite Zset.In_union in IN.
    destruct IN; eauto.
Qed.

Lemma Zset_incl_add : forall p s1 s2, Zset.incl (Zset.add p s1) s2 = true <->
                                      Zset.In p s2 /\ Zset.incl s1 s2 = true.
Proof.
  intros.
  split; intros; repeat rewrite Zset_incl_spec in *.
  - split.
    + apply H.
      rewrite Zset.In_add. eauto.
    + intros p' IN;
      apply H;
      rewrite Zset.In_add; eauto.
  - destruct H as [H1 H2].
    intros p' IN.
    rewrite Zset.In_add in IN.
    destruct IN; subst; eauto.
Qed.

Lemma labToVal_valToLab_id_SOP : forall l t m, labToVal l t m -> valToLab t m = l.
Proof.
  unfold labToVal, valToLab ; intros.
  destruct H as (vs & b & NEQ & KERNEL & E & ARR & IN). subst.
  destruct ARR as [? t LOAD SEQ ?]. subst.
  unfold load in *.
  destruct (Mem.get_frame m b) as [fr|] eqn:FRAME; try congruence.
  destruct fr as [|len fr]; try solve [inv LOAD].
  unfold read_m in LOAD. simpl in LOAD. inv LOAD.
  rewrite Nat2Z.id.
  change (take (length (map Vint vs : list (val privilege))) fr)
    with (take (length (map Vint vs : list (val privilege)))
               (dropZ 1 ((Vint (Z.of_nat (length (map Vint vs : list (val privilege)))), t) :: fr))).
  exploit memseq_get_frame; eauto; try omega.
  intros H.
  unfold Atom in H. (* Invisible, grr... *)
  rewrite <- H.
  clear - IN.
  assert (IN' : forall a, (In a vs \/ Zset.In a Zset.empty) <-> Zset.In a l).
  { intuition.
    - rewrite <- IN. eauto.
    - unfold Zset.In in *.
      rewrite Zset.elements_empty in *.
      simpl in *. intuition.
    - left. rewrite IN. eauto. }
  clear IN. rename IN' into IN.
  gdep Zset.empty. gdep l.
  induction vs as [|p vs IH]; simpl; eauto.
  - intros.
    apply Zset.antisym; rewrite Zset_incl_spec; intros p H; firstorder.
  - intros.
    apply IH. intros a.
    rewrite <- IN.
    intuition; rewrite Zset.In_add in *; eauto; intuition.
Qed.

Lemma genBot_spec_SOP : forall m0 (Hm0: mem_def_on_cache cblock m0) (Q:HProp),
   HT cblock genBot
      (fun m s => extends m0 m /\
                  (forall m1 z t,
                     extends m m1 -> labToVal bot z m1 -> Q m1 ((z,t):::s)))
      Q.
Proof.
  intros.
  eapply HT_compose_flip.
  eapply alloc_array_spec_wp; eauto.
  eapply HT_strengthen_premise.
  eapply push_spec_wp; eauto.
  intros m s (EXT & POST).
  do 3 eexists.
  repeat (split; eauto; try omega).
  intros b m1 t EXT' VALID [t' LOAD] FRESH KERNEL.
  apply POST; eauto.
  eapply extends_mem_def_on_cache with (m' := m) in Hm0; eauto using extends_trans.
  destruct Hm0.
  eexists [], b.
  repeat (split; eauto); try congruence.
  - econstructor; try constructor.
    rewrite LOAD; eauto.
  - intros [].
  - intros IN.
    simpl in IN.
    unfold Zset.In in *.
    rewrite Zset.elements_empty in IN.
    inversion IN.
Qed.

Lemma genJoin_spec_SOP: forall m0 (Hm0: mem_def_on_cache cblock m0) (Q: HProp),
       HT cblock genJoin
         (fun m s =>
          exists s0 l z t l' z' t',
             s = (z, t) ::: (z', t') ::: s0 /\
             extends m0 m /\
             labToVal l z m /\ labToVal l' z' m /\
             (forall m1 zz' t, extends m m1 -> labToVal (l \_/ l') zz' m1 ->
                         Q m1 ((zz', t) ::: s0)))
         Q.
Proof.
  intros.
  eapply HT_strengthen_premise.
  eapply concat_arrays_spec_wp ; eauto.
  go_match.
  destruct H as (s0 & l & v & t & l' & v' & t' & ? & EXT & Hl & Hl' & POST). subst.
  unfold labToVal in *.
  destruct Hl as (c & b & Nb & Kb & ? & ARR & IN).
  destruct Hl' as (c' & b' & Nb' & Kb' & ? & ARR' & IN'). subst.
  do 7 eexists. repeat (split; try solve [intuition eauto]).
  intros r m1 t'' EXT' ARR'' FRESH Kr.
  apply POST; eauto.
  eexists (c' ++ c), r.
  eapply extends_mem_def_on_cache in Hm0; eauto. destruct Hm0.
  rewrite map_app.
  repeat (split; [solve [eauto | congruence]|]).
  intros a.
  rewrite in_app_iff, Zset.In_union, IN, IN'. intuition.
Qed.

Lemma incl_val_list_subset_b : forall l1 l2,
                                 incl l1 l2 <->
                                 val_list_subset_b l1 l2 = true.
Proof.
  intros. split.
  - intros. eapply forallb_forall. intros.
    eapply H in H0.  eapply existsb_exists.
    exists x; intuition.
    destruct (EquivDec.equiv_dec x x); try congruence.
  - intros.
    unfold incl. intros.
    unfold val_list_subset_b in H.
    eapply forallb_forall in H; eauto.
    unfold val_list_in_b in H.
    eapply existsb_exists in H.
    destruct H. intuition.
    destruct (EquivDec.equiv_dec a x) in H2; try congruence.
Qed.

Lemma Zsetincl_val_list_subset : forall l l' x x',
                                 forall (Hxl : forall a, In a x <-> Zset.In a l)
                                        (Hx'l' : forall a, In a x' <-> Zset.In a l'),
                                   Zset.incl l l' =
                                   val_list_subset_b (map Vint x) (map Vint x').
Proof.
  intros.
  rewrite Bool.eq_iff_eq_true.
  split; intros.
  - apply Zset.incl_spec in H.
    eapply incl_val_list_subset_b; eauto.
    unfold incl, Zset.In in *.
    intros a IN.
    rewrite in_map_iff in *.
    destruct IN as (i & ? & IN). subst.
    eexists. split; eauto.
    rewrite Hxl in IN.
    rewrite Hx'l'. eauto.

  - apply Zset.incl_spec.
    intros a IN.
    unfold Zset.In in *.
    eapply Hx'l'.
    rewrite <- Hxl in IN.
    apply incl_val_list_subset_b in H.
    eapply in_map in IN. apply H in IN.
    rewrite in_map_iff in IN. destruct IN. intuition congruence.
Qed.

Lemma genFlows_spec_SOP: forall m0 (Hm0: mem_def_on_cache cblock m0) (Q: HProp),
                   HT cblock genFlows
                       (fun m s =>
                          exists l l' z z' t t' s0,
                            extends m0 m /\
                            labToVal l z m /\ labToVal l' z' m /\
                            s = (z,t):::(z',t'):::s0 /\
                            forall t'',
                            Q m ((boolToVal(l <: l'),t''):::s0))
                       Q.
Proof.
  intros.
  unfold genFlows; intros.
  eapply HT_strengthen_premise.
  eapply subset_arrays_spec_wp; eauto.
  intros m s (l & l' & z & z' & t & t' & s0 & EXT & Hl & Hl' & ? & POST). subst.
  destruct Hl as (c & b & Nb & Kb & ? & ARR & IN).
  destruct Hl' as (c' & b' & Nb' & Kb' & ? & ARR' & IN'). subst.
  eexists b, b', (map Vint c), (map Vint c'). do 4 eexists; repeat split; eauto.
  intros t''.
  erewrite <- Zsetincl_val_list_subset; eauto.
Qed.

Global Instance SOPwf (fh: list Instr) : WfConcreteLattice cblock Zset.t ZsetLat SOPClatt :=
{ labToVal_cache := labToVal_cache_SOP
; labToVal_valToLab_id := labToVal_valToLab_id_SOP
; labToVal_inj := labToVal_inj_SOP
; labToVal_extension_comp := labToVal_extension_comp_SOP
; genBot_spec := genBot_spec_SOP
; genJoin_spec := genJoin_spec_SOP
; genFlows_spec := genFlows_spec_SOP
}.

End SOP.
