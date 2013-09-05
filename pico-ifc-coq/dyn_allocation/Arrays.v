(** Code, specifications, proofs for manipulating arrays in kernel memory *)

Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import LibTactics.
Import ListNotations.

Require Import Memory.
Require Import Instr.
Require Import Lattices.
Require Import Concrete.
Require Import CodeGen.
Require Import CodeTriples.
Require Import CodeSpecs.
Require Import Concrete.
Require Import ConcreteExecutions.
Require Import ConcreteMachine.
Require Import Determinism.
Require Import Coq.Arith.Compare_dec.

(* Everything to do with machine execution and triples has to be parameterized over SysTable. *)
Section with_cblock.

Variable cblock : block privilege.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.

Local Notation val := (val privilege).
Local Notation Atom := (Atom val privilege).
Local Notation memory := (Mem.t Atom privilege).
Local Notation PcAtom := (PcAtom val).
Local Notation block := (block privilege).

(* MOVE *)
Lemma extends_valid_address: forall b m m' off
                                    (VALID : valid_address b off m)
                                    (EXT : extends m m'),
                               valid_address b off m'.
Proof.
  intros.
  unfold valid_address in *.
  destruct VALID.
  eauto using extends_load.
Qed.

Ltac apply_wp :=
  try unfold pop, nop, push, dup, swap;
  match goal with
  | |- HT _ [Store] _ _ => eapply store_spec_wp'
  | |- HT _ [Add] _ _  => eapply add_spec_wp'
  | |- HT _ [Dup ?N] _ _ => eapply dup_spec_wp
  | |- HT _ [Swap ?N] _ _ => eapply swap_spec_wp
  | |- HT _ [Load] _ _ => eapply load_spec_wp'
  | |- HT _ [Push ?N] _ _ => eapply push_spec_wp
  | |- HT _ [Pop] _ _ => eapply pop_spec_wp
  end;
  simpl.

Ltac build_vc wptac :=
  let awp := (try apply_wp; try wptac) in
  try (eapply HT_compose_flip; [(build_vc wptac; awp)| (awp; eapply HT_strengthen_premise; awp)]).

(* This version doesn't progress past introductions, which makes it useful when
   we need to do some manual work after an introduction but before doing an eexists *)
Ltac split_vc' :=
  (try subst; simpl;
   match goal with
   | H: exists X,_ |- _ => (destruct H; split_vc')
   | H: ?P /\ ?Q |- _ => (destruct H; split_vc')
   | |- exists X, _ => (eexists; split_vc')
   | |- ?P /\ ?Q => (split; [(eauto; try (zify; omega);fail) | split_vc'])
   | _ => (eauto; try (zify; omega))
   end).

(* This version is more aggressive. *)
Ltac split_vc :=
  (try subst; simpl;
   match goal with
   | H: exists X,_ |- _ => (destruct H; split_vc)
   | H: ?P /\ ?Q |- _ => (destruct H; split_vc)
   | |- forall P, _ => (intro; try subst; split_vc)
   | |- exists X, _ => (eexists; split_vc)
   | |- ?P /\ ?Q => (split; [(eauto; try (zify; omega);fail) | split_vc])
   | _ => (eauto; try (zify; omega))
   end).

Section with_hints.  (* Limit hints to this section. *)

(* These are intended to work with split_vc. *)
Hint Resolve extends_refl.
Hint Resolve extends_trans.
Hint Resolve extends_valid_address.

(* MOVE *)
Lemma valid_address_store_l :
  forall b off a m m'
         (STORE : store b off a m = Some m'),
    valid_address b off m.
Proof.
  unfold store, valid_address, load.
  intros.
  destruct (Mem.get_frame m b) as [fr|] eqn:FRAME; try congruence.
  destruct (upd_m off a fr) as [fr'|] eqn:FRAME'; try congruence.
  clear - FRAME'.
  unfold upd_m, read_m in *.
  destruct (off <? 0); try congruence.
  gdep fr. gdep fr'. gdep (Z.to_nat off).
  clear.
  intros off.
  induction off as [|off IH]; intros fr' fr H; destruct fr as [|a' fr]; simpl in *; try congruence; eauto.
  destruct (update_list off a fr) as [fr''|] eqn:FRAME''; try congruence.
  eapply IH; eauto.
Qed.

Lemma valid_address_store_r :
  forall b off a m m'
         (STORE : store b off a m = Some m'),
    valid_address b off m'.
Proof.
  intros.
  eauto using valid_address_store_l, valid_address_upd.
Qed.

(* TODO: Move to CodeSpecs.v *)
Lemma extends_update :
  forall m m1 m2 b off a
         (EXT : extends m m1)
         (STORE : store b off a m1 = Some m2)
         (INVALID : ~ valid_address b off m),
    extends m m2.
Proof.
  intros.
  intros b' fr' FRAME'.
  assert (b' <> b).
  { intros NEQ.
    subst.
    destruct (load b off m) as [r|] eqn:LOAD.
    - apply INVALID. unfold valid_address. eauto.
    - eapply valid_address_store_l in STORE.
      destruct STORE as [res RES].
      unfold load in *.
      rewrite FRAME' in LOAD.
      apply EXT in FRAME'.
      rewrite FRAME' in RES.
      congruence. }
  apply EXT in FRAME'.
  rewrite <- FRAME'.
  eapply get_frame_store_neq; eauto.
Qed.

Hint Resolve extends_update.

(* Memory copy.  *)

(* Initial stack:  count :: dst0 :: src0 :: _
   Final stack:    0 :: dst0 :: src0 :: _
   Side Effects: copies (src0,src0+count] to (dst0,dst0+count]  (provided these regions are disjoint) *)

Definition copy :=
  genRepeat ([Dup 2] ++ (* src0 :: count :: dst0 :: src0 :: _ *)
             [Dup 1] ++ (* count :: src0 :: count :: dst0 :: src0 :: _ *)
             [Add] ++   (* src0+count :: count :: dst0 :: src0 :: _ *)
             [Load] ++  (* mem[src0+count] :: count :: dst0 :: src0 :: _ *)
             [Dup 2] ++ (* dst0 :: mem[src0+count] :: count :: dst0 :: src0 :: _ *)
             [Dup 2] ++ (* count :: dst0 :: mem[src0+count] :: count :: dst0 :: src0 :: _ *)
             [Add] ++   (* dst0+count :: mem[src0+count] :: count :: dst0 :: src0 :: _ *)
             [Store]).

(* The loop invariant for copy. *)
Definition Icopy (sz:Z) bdst odst bsrc osrc m0 s0 :=
  fun m s =>
    exists cnt, s = (Vint cnt,handlerTag):::(Vptr bdst odst,handlerTag):::(Vptr bsrc osrc,handlerTag):::s0 /\
    (cnt <= sz) /\
    (forall z, osrc < z <= osrc+cnt -> valid_address bsrc z m) /\
    (forall z, odst < z <= odst+cnt -> valid_address bdst z m) /\
    (bdst <> bsrc) /\
    (Mem.stamp bdst = Kernel) /\
    (Mem.stamp bsrc = Kernel) /\
    (forall z, cnt < z <= sz -> load bsrc (osrc+z) m = load bdst (odst+z) m) /\
    (forall z, ~ (odst+cnt < z <= odst+sz) -> load bdst z m = load bdst z m0) /\
    (forall b, b <> bdst -> Mem.get_frame m b = Mem.get_frame m0 b).

Lemma copy_spec_wp : forall (Q : memory -> stack -> Prop),
  HT cblock copy
  (fun m s => exists sz bdst odst bsrc osrc s0,
                0 <= sz /\
                s = (Vint sz,handlerTag):::(Vptr bdst odst,handlerTag):::(Vptr bsrc osrc,handlerTag):::s0 /\
                (forall z, osrc < z <= osrc+sz -> valid_address bsrc z m) /\
                (forall z, odst < z <= odst+sz -> valid_address bdst z m) /\
                (bdst <> bsrc) /\
                Mem.stamp bdst = Kernel /\
                Mem.stamp bsrc = Kernel /\
                (forall m1,
                   (forall z, 0 < z <= sz -> load bsrc (osrc+z) m1 = load bdst (odst+z) m1) /\
                   (forall z, ~ (odst < z <= odst+sz) -> load bdst z m1 = load bdst z m) /\
                   (forall b, b <> bdst -> Mem.get_frame m1 b = Mem.get_frame m b) ->
                   Q m1 ((Vint 0,handlerTag):::(Vptr bdst odst,handlerTag):::(Vptr bsrc osrc,handlerTag):::s0)))
  Q.
Proof.
  intros. unfold copy.
  eapply HT_strengthen_premise with
  (fun m s => exists sz bdst odst bsrc osrc s0 m0,
                0 <= sz /\
                m = m0 /\
                s = (Vint sz,handlerTag):::(Vptr bdst odst,handlerTag):::(Vptr bsrc osrc,handlerTag):::s0 /\
                (forall z, osrc < z <= osrc+sz -> valid_address bsrc z m) /\
                (forall z, odst < z <= odst+sz -> valid_address bdst z m) /\
                (bdst <> bsrc) /\
                Mem.stamp bdst = Kernel /\
                Mem.stamp bsrc = Kernel /\
                (forall m1,
                   (forall z, 0 < z <= sz -> load bsrc (osrc+z) m1 = load bdst (odst+z) m1) /\
                   (forall z, ~ (odst < z <= odst+sz) -> load bdst z m1 = load bdst z m) /\
                   (forall b, b <> bdst -> Mem.get_frame m1 b = Mem.get_frame m b) ->
                   Q m1 ((Vint 0,handlerTag):::(Vptr bdst odst,handlerTag):::(Vptr bsrc osrc,handlerTag):::s0)));
    [|solve [split_vc]].
  eapply HT_forall_exists. intro sz.
  eapply HT_forall_exists. intro bdst.
  eapply HT_forall_exists. intro odst.
  eapply HT_forall_exists. intro bsrc.
  eapply HT_forall_exists. intro osrc.
  eapply HT_forall_exists. intro s0.
  eapply HT_forall_exists. intro m0.
  eapply HT_fold_constant_premise; intro.
  rename Q into Q0.
  eapply HT_consequence' with
    (P := (fun m s => exists s', s = CData(Vint sz,handlerTag)::s' /\ Icopy sz bdst odst bsrc osrc m0 s0 m s))
    (Q := (fun m s => exists s', s = CData(Vint 0,handlerTag)::s' /\ Icopy sz bdst odst bsrc osrc m0 s0 m s)).
  - eapply genRepeat_spec; eauto.
    intros.
    unfold Icopy.
    build_vc ltac:idtac; try solve [split_vc].
    intros m s (s' & Hs' & i' & ? & ? & VALIDSRC & VALIDDST & ? & ? & ? & COPY & REST & ?).
    assert (i' = i) by congruence. subst i'. clear s' Hs'.
    subst.
    simpl.
    repeat (eexists; split; eauto).
    exploit (VALIDSRC (i + osrc)); try omega. intros [val Hval].
    exploit (VALIDDST (i + odst)); try omega. intros [val' Hval'].
    eapply load_some_store_some in Hval'. destruct Hval' as [m' Hm'].
    do 37 (try eexists); simpl; eauto; try omega. (* Can break if given bigger number *)
    repeat split; eauto.
    + intros.
      eapply valid_address_upd; eauto.
      apply VALIDSRC. omega.
    + intros.
      eapply valid_address_upd; eauto.
      apply VALIDDST. omega.
    + intros.
      destruct (Z.eq_dec i z) as [ZEQ | ZNEQ].
      * subst.
        replace (odst + z) with (z + odst) by omega.
        erewrite (load_store_new Hm').
        rewrite <- Hval.
        replace (osrc + z) with (z + osrc) by ring.
        eapply load_store_old; eauto.
        congruence.
      * do 2 (erewrite (load_store_old Hm'); eauto; try congruence).
        2: (intros contra; inversion contra; omega).
        eapply COPY. omega.
    + intros.
      erewrite (load_store_old Hm'); eauto; try congruence.
      2: (intros contra; inversion contra; omega).
      apply REST. omega.
    + intros.
      erewrite (get_frame_store_neq _ _ _ _ _ _ _ _ Hm'); eauto.
  - split_vc.
    unfold Icopy.
    repeat split; auto.
    exists sz. intuition (solve [eauto | omega]).
  - unfold Icopy.
    split_vc.
    match goal with
      | H : _ ::: _ = _ ::: _ |- _ => inv H
    end.
    replace (odst + 0) with odst in * by omega.
    eauto.
Qed.

(* A (counted) array is a sequence of values in memory, proceeded by their count:

        -----------
a ----> |    n    |
        -----------
        |  v_1    |
        -----------
        |  ...    |
        -----------
        |  v_n    |
        -----------

*)


Inductive memseq (m:memory) b : Z -> list val -> Prop :=
| memseq_nil : forall z, memseq m b z nil
| memseq_cons : forall z v vs, load b z m = Some (v, handlerTag) -> memseq m b (z+1) vs -> memseq m b z (v::vs)
.

Lemma memseq_valid : forall m b a vs,
  memseq m b a vs ->
  forall z, a <= z < a + Z.of_nat(length vs) -> valid_address b z m.
Proof.
  induction 1; intros.
  simpl in H. exfalso; omega.
  simpl in H1.
  destruct (Z.eq_dec z z0).
  { subst. econstructor. eauto. }
  eapply IHmemseq. zify; omega.
Qed.

Hint Resolve memseq_valid.

Lemma memseq_read : forall m b a vs,
  memseq m b a vs ->
  forall z, a <= z < a + Z.of_nat(length vs) -> exists v, load b z m = Some(v,handlerTag).
Proof.
  induction 1; intros.
  simpl in H. exfalso; omega.
  simpl in H1.
  destruct (Z.eq_dec z z0).
  { subst. eexists; eauto. }
  eapply IHmemseq. zify; omega.
Qed.

Lemma memseq_app: forall m b a vs1 vs2,
  memseq m b a (vs1 ++ vs2) <-> (memseq m b a vs1 /\ memseq m b (a + Z.of_nat(length vs1)) vs2).
Proof.
  intros. split.
  - generalize dependent a.
    induction vs1; intros.
    + simpl in *.
      split. constructor.
      replace (a+0) with a by ring. auto.
    + simpl in H.
      inv H.
      destruct (IHvs1 (a0+1) H4).
      split.
      econstructor; eauto.
      simpl (length (a::vs1)).
      replace (a0 + Z.of_nat (S (length vs1))) with (a0 + 1 + Z.of_nat(length vs1)) by (zify;omega).
      assumption.
  - generalize dependent a.
    induction vs1; intros.
    + simpl in *. inv H. replace (a+0) with a in H1 by ring. auto.
    + inv H. simpl. inv H0. econstructor; eauto.
      eapply IHvs1. split. auto. simpl (length (a::vs1)) in H1.
      replace (a0 + 1 + Z.of_nat (length vs1)) with (a0 + Z.of_nat(S(length vs1))) by (zify;omega).
      assumption.
Qed.

Lemma memseq_eq :
  forall m1 m2 b1 b2 a1 a2 vs
         (LOAD : forall z, 0 <= z < Z.of_nat (length vs) ->
                           load b1 (a1+z) m1 = load b2 (a2+z) m2)
         (SEQ : memseq m1 b1 a1 vs),
    memseq m2 b2 a2 vs.
Proof.
  intros.
  generalize dependent a2.
  induction SEQ.
  - intros. constructor.
  - intros.
    assert (Hz : load b1 z m1 = load b2 a2 m2).
    { replace z with (z+0) by ring. replace a2 with (a2+0) by ring.
      eapply LOAD. simpl. zify; omega. }
    destruct (load b2 a2 m2) as [[v0 l0]|] eqn:E; try congruence.
    rewrite Hz in H. inv H.
    econstructor; eauto.
    eapply IHSEQ. intros.
    replace (z+1 + z0) with (z+(1+z0)) by omega.
    replace (a2+1 + z0) with (a2+ (1+z0)) by omega.
    eapply LOAD. simpl (length (v::vs)). zify; omega.
Qed.

Lemma memseq_drop :
  forall ms b z p vs
         (MEM : memseq ms b z vs),
    memseq ms b (z + Z.of_nat p) (drop p vs).
Proof.
  intros.
  gdep z. gdep p.
  induction vs as [|v vs IH]; intros p z MEM.
  - destruct p; constructor.
  - destruct p.
    * simpl.
      rewrite Zplus_comm. auto.
    * rewrite Nat2Z.inj_succ in *.
      inv MEM.
      replace (z + Z.succ (Z.of_nat p)) with (z + 1 + Z.of_nat p); try omega.
      apply IH. auto.
Qed.

Inductive memarr (m:memory) b (vs:list val) : Prop :=
| memarr_i : forall c
                    (LOAD : load b 0 m = Some (Vint (Z_of_nat c), handlerTag))
                    (SEQ : memseq m b 1 vs)
                    (LEN : c = length vs),
               memarr m b vs.

(* Array allocation.  *)

(* Initial stack: count :: _
   Final stack:  ptr-to-array :: _
   Side effects: allocates fresh array of size count *)

Definition alloc_array:= push 0 ++ [Dup 1] ++ push 1 ++ [Add] ++ [Alloc] ++ dup ++ [Swap 2] ++ [Swap 1] ++ [Store].

(* a direct proof in wp form this time, just for variety. *)
Lemma alloc_array_spec_wp: forall (Q : memory -> stack -> Prop),
  HT cblock alloc_array
     (fun m s => exists cnt s0,
                   s = (Vint cnt,handlerTag):::s0 /\
                   cnt >= 0 /\
                   (forall b m1,
                      extends m m1 ->
                      (forall p, 0 < p <= cnt -> valid_address b p m1) ->
                      load b 0 m1 = Some (Vint cnt, handlerTag) ->
                      Mem.get_frame m b = None ->
                      Mem.stamp b = Kernel ->
                      Q m1 ((Vptr b 0,handlerTag):::s0)))
     Q.
Proof.
  intros.
  unfold alloc_array.
  Opaque Z.add. (* not sure why this is necessary this time *)
  unfold alloc_array.
  build_vc ltac: (try apply alloc_spec_wp; eauto).
  intros m s (cnt & s0 & ? & ? & H).
  subst. simpl.
  clear stamp_cblock.
  do 31 (try eexists; simpl; eauto); try omega.
  assert (VALID : valid_address b 0 m0).
  { eexists (Vint 0, handlerTag).
    erewrite load_alloc; eauto.
    simpl.
    destruct (EquivDec.equiv_dec b b); try congruence.
    destruct (Z_lt_dec 0 (1 + cnt)); try omega.
    reflexivity. }
  eapply valid_store in VALID. destruct VALID.
  assert (ALLOC' := H0).
  unfold c_alloc, alloc in H0.
  match goal with
    | H : match ?B with _ => _ end = Some _ |- _ =>
      destruct B; inv H
  end.
  repeat eexists; simpl; eauto.
  - eapply Mem.alloc_stamp; eauto.
  - assert (FRESH : Mem.get_frame m b = None).
    { eapply Mem.alloc_get_fresh; eauto. }
    apply H; eauto.
    + intros b' fr' FRAME'.
      assert (b <> b') by congruence.
      eapply get_frame_store_neq in H2; eauto.
      eapply alloc_get_frame_old in H4; eauto.
      congruence.
    + intros.
      unfold c_alloc in ALLOC'.
      eexists (Vint 0, handlerTag).
      erewrite load_store_old; eauto.
      * erewrite (load_alloc (b := b)); eauto.
        destruct (EquivDec.equiv_dec b b); try congruence.
        destruct (Z_le_dec 0 p); try omega.
        destruct (Z_lt_dec p (1 + cnt)); try omega.
        reflexivity.
      * intros contra.
        inv contra.
        omega.
    + eapply load_store_new; eauto.
    + eapply Mem.alloc_stamp; eauto.
Qed.
Transparent Z.add.

(* Sum array lengths *)

(* Initial stack:  array1 :: array2 :: _
   Final stack:    (l1+l2) :: array1 :: array2 :: _
      where l1,l2 are lengths of array1,array2
   Side effects: none
*)

Definition sum_array_lengths := [Dup 1] ++ [Load] ++ [Dup 1] ++ [Load] ++ [Add].

Lemma sum_array_lengths_spec_wp : forall Q,
  HT cblock sum_array_lengths
     (fun m s => exists a1 a2 s0 l1 l2,
                 s = (Vptr a2 0,handlerTag):::(Vptr a1 0,handlerTag):::s0 /\
                 load a2 0 m = Some (Vint l2, handlerTag) /\
                 load a1 0 m = Some (Vint l1, handlerTag) /\
                 Mem.stamp a1 = Kernel /\
                 Mem.stamp a2 = Kernel /\
                 Q m ((Vint (l2+l1),handlerTag):::(Vptr a2 0,handlerTag):::(Vptr a1 0,handlerTag):::s0))
      Q.
Proof.
  intros. unfold sum_array_lengths.
  build_vc ltac:idtac.
  split_vc.
Qed.


(* Concatenate two existing arrays into a freshly allocated new array. *)

(* Initial stack: array1::array2::_
   Final stack:   r::_
        where r is pointer to newly allocated array
   Side effects: allocates new array and concatenates existing contents into it.  *)

Definition concat_arrays :=      (* a2 a1 *)
     sum_array_lengths           (* (l2+l1) a2 a1 *)
  ++ alloc_array                 (* r a2 a1 *)
  ++ [Dup 2]                     (* a1 r a2 a1 *)
  ++ [Dup 1]                     (* r a1 r a2 a1 *)
  ++ [Dup 1]                     (* a1 r a1 r a2 a1 *)
  ++ [Load]                      (* l1 r a1 r a2 a1 *)
  ++ copy                        (* 0 r a1 r a2 a1 *)
  ++ pop                         (* r a1 r a2 a1 *)
  ++ [Dup 1]                     (* a1 r a1 r a2 a1 *)
  ++ [Load]                      (* l1 r a1 r a2 a1 *)
  ++ [Add]                       (* (l1+r) a1 r a2 a1 *)
  ++ [Swap 1]                    (* a1 (l1+r) r a2 a1 *)
  ++ pop                         (* (l1+r) r a2 a1 *)
  ++ [Dup 2]                     (* a2 (l1+r) r a2 a1 *)
  ++ [Swap 1]                    (* (l1+r) a2 r a2 a1 *)
  ++ [Dup 1]                     (* a2 (l1+r) a2 r a2 a1 *)
  ++ [Load]                      (* l2 (l1+r) a2 r a2 a1 *)
  ++ copy                        (* 0 (l1+r) a2 r a2 a1 *)
  ++ pop                         (* (l1+r) a2 r a2 a1 *)
  ++ pop                         (* a2 r a2 a1 *)
  ++ pop                         (* r a2 a1 *)
  ++ [Swap 2]                    (* a2 a1 r *)
  ++ pop                         (* a1 r *)
  ++ pop                         (* r *)
.


Lemma concat_arrays_spec_wp : forall (Q :memory -> stack -> Prop),
  HT cblock
   concat_arrays
   (fun m s => exists a2 a1 vs1 vs2 s0,
                 s = (Vptr a2 0,handlerTag):::(Vptr a1 0,handlerTag):::s0 /\
                 memarr m a1 vs1 /\ memarr m a2 vs2 /\
                 Mem.stamp a1 = Kernel /\ Mem.stamp a2 = Kernel /\
                 (forall r m1,
                    extends m m1 ->
                    memarr m1 r (vs1 ++ vs2) ->
                    Mem.get_frame m r = None ->
                    Mem.stamp r = Kernel ->
                    Q m1 ((Vptr r 0,handlerTag):::s0)))
   Q.
Proof.
  intros. unfold concat_arrays.

  build_vc ltac:(try apply copy_spec_wp; try apply alloc_array_spec_wp; try apply sum_array_lengths_spec_wp).

  intros m s (a2 & a1 & vs1 & vs2 & s0 & ? & ARR1 & ARR2 & K1 & K2 & POST).
  destruct ARR1. destruct ARR2.
  split_vc'.
  intros b m1 EXT VALID LOADSUM FRESH KERNEL.
  assert (a1 <> b).
  { intros contra. subst. unfold load in *.
    rewrite FRESH in LOAD.
    congruence. }
  assert (a2 <> b).
  { intros contra. subst. unfold load in *.
    rewrite FRESH in LOAD0.
    congruence. }

  do 8 (try eexists); eauto.
  eexists (Vint (Z.of_nat (length vs1)), handlerTag).
  split_vc.
  split; eauto using extends_load.
  split_vc.
  split; split_vc; try omega.
  split.
  { intros.
    eapply extends_valid_address; eauto.
    eapply memseq_valid; eauto.
    omega. }
  split.
  { intros. apply VALID. omega. }
  split; try congruence.
  split; auto.
  split_vc.
  assert (LOADm0m1 : forall b' off,
                       b' <> b ->
                       load b' off m0 = load b' off m1).
  { unfold load.
    intros.
    rewrite H3; trivial. }
  split.
  { assert (LOAD'' := LOAD).
    eapply extends_load with (m3 := m1) in LOAD''; eauto.
    cut (load a1 0 m0 = load a1 0 m1).
    { intros E. rewrite E. eassumption. }
    unfold load.
    rewrite H3; trivial. }
  split_vc.
  split.
  { assert (LOAD'' := LOAD0).
    eapply extends_load with (m3 := m1) in LOAD''; eauto.
    cut (load a2 0 m0 = load a2 0 m1).
    { intros E. rewrite E. eassumption. }
    unfold load.
    rewrite H3; trivial. }
  split_vc.
  split; try (split; try solve [eauto]); try omega.
  split.
  { simpl. intros.
    eapply memseq_valid with (z := z) in SEQ0; try omega.
    exploit extends_valid_address; eauto.
    unfold valid_address in *.
    rewrite LOADm0m1; eauto. }
  split.
  { intros.
    unfold valid_address in *.
    rewrite H2; try omega.
    apply VALID. omega. }
  split_vc.
  apply POST; trivial.
  - intros b' fr' FRAME'.
    rewrite H6; try congruence.
    rewrite H3; try congruence.
    eauto.
  - econstructor; eauto.
    + rewrite H5; try omega.
      rewrite H2; try omega.
      rewrite LOADSUM.
      repeat f_equal.
      rewrite app_length. zify. omega.
    + rewrite memseq_app.
      split.
      * apply memseq_eq with (m1 := m) (b1 := a1) (a1 := 1); eauto.
        intros.
        rewrite H5; try omega.
        rewrite <- H1; try omega.
        rewrite LOADm0m1; try congruence.
        assert (VALID' : valid_address a1 (1 + z) m).
        { eapply memseq_valid; eauto. omega. }
        destruct VALID' as [a VALID'].
        rewrite VALID'.
        symmetry.
        eapply extends_load; eauto.
      * apply memseq_eq with (m1 := m) (b1 := a2) (a1 := 1); eauto.
        intros.
        replace (1 + Z.of_nat (length vs1) + z) with (Z.of_nat (length vs1) + 0 + (1 + z)) by ring.
        rewrite <- H4; try omega.
        assert (LOADm2m0 : load a2 (1 + z) m2 = load a2 (1 + z) m0).
        { unfold load. rewrite H6; trivial. }
        rewrite LOADm2m0.
        rewrite LOADm0m1; try congruence.
        assert (VALID' : valid_address a2 (1 + z) m).
        { eapply memseq_valid; eauto. omega. }
        destruct VALID' as [a VALID'].
        rewrite VALID'.
        symmetry.
        eapply extends_load with (m3 := m); eauto.
Qed.

(* Foldr over an array. *)

(* Initial stack:   a::S
   Final stack:     r::S
       where gen_n assumes _::S and generates v::_::S  with v the initial accumulator value
       where gen_f assumes x::v::_::_::_::S and generates v'::_::_::_::S with v' the new accumulator value
       and r is overall accumulator value for entire list. *)
Definition fold_array_body gen_f :=   (* i v a S *)
      [Dup 1]                         (* v i v a S *)
   ++ [Dup 3]                         (* a v i v a S *)
   ++ [Dup 2]                         (* i a v i v a S *)
   ++ [Add]                           (* i+a v i v a S *)
   ++ [Load]                          (* x v i v a S *)
   ++ gen_f                           (* v' i v a S *)
   ++ [Swap 2]                        (* v i v' a S *)
   ++ pop                             (* i v' a S *)
.

Definition fold_array gen_n gen_f :=     (* a S *)
      gen_n                              (* v a S *)
  ++  [Dup 1]                            (* a v a S *)
  ++  [Load]                             (* l v a S *)
  ++  genRepeat                          (* i v a S *)
         (fold_array_body gen_f)          (* i v' a S *)
  ++ pop                                 (* r a S *)
  ++ [Swap 1]                            (* a r S *)
  ++ pop                                 (* r S *)
.



(* Invariant for fold array body *)
Definition Ifab (f : memory -> stack -> val -> val -> val) (n: memory -> stack -> val)
                (a:block) (vs:list val) m0 s0 :=
    fun m s =>
      exists i v,
        i <= Z.of_nat (length vs) /\
        memarr m a vs /\
        Mem.stamp a = Kernel /\
        m = m0 /\
        s = (Vint i,handlerTag):::(v,handlerTag):::(Vptr a 0,handlerTag):::s0  /\
        v = fold_right (f m0 s0) (n m0 s0) (dropZ i vs).

Lemma fab_spec : forall gen_f f n a vs m0 s0 i,
  (forall (Q: memory -> stack -> Prop),
  HT cblock gen_f
     (fun m s => exists x v ign0 ign1 ign2,
                   s = (x,handlerTag):::(v,handlerTag):::
                       (ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0 /\
                   m = m0 /\
                   Q m (((f m0 s0) x v,handlerTag):::
                       (ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0))
      Q) ->
  HT cblock (fold_array_body gen_f)
  (fun m s => exists s', s = (Vint i,handlerTag):::s' /\ i > 0 /\ Ifab f n a vs m0 s0 m s)
  (fun m s => exists s', s = (Vint i,handlerTag):::s' /\ Ifab f n a vs m0 s0 m ((Vint (Z.pred i),handlerTag):::s')).
Proof.
  intros.
  unfold fold_array_body.
  build_vc ltac:(try apply H).
  split_vc.
  destruct H1 as [i' [ v' [? [? [? [? [? ?]]]]]]]. subst.  inv H5.  inv H2.
  destruct (memseq_read _ _ _ _ SEQ i') as [v ?]; try omega.
  split_vc.
  replace (i' + 0) with i' by ring.
  split_vc.
  econstructor.
  eexists.
  split.  instantiate (1:= Zpred i'). omega.
  split. econstructor; eauto.
  split_vc.
  unfold dropZ. destruct (i' <? 0) eqn:E. apply Z.ltb_lt in E. omega.
  destruct (Z.pred i' <? 0) eqn:E'.  apply Z.ltb_lt in E'. omega.
  apply Z.ltb_ge in E. apply Z.ltb_ge in E'.
  remember (Z.to_nat (Z.pred i')) as p.
  replace (Z.to_nat i') with (S p).
  2: subst p; zify; do 2 (rewrite Z2Nat.id; eauto); omega.

  (* Here we go *)
  cut (drop p vs =  v::drop (S p) vs).
  { intros P.
    rewrite P.  auto. }
  apply (memseq_drop _ _ _ p) in SEQ.
  generalize (@drop_cons _ p vs).
  intros HH.
  assert (p < length vs)%nat.
  { zify.
    rewrite Z2Nat.id in Heqp; omega. }
  destruct HH as [v' Hv']; auto.
  rewrite Hv' in SEQ.
  inv SEQ.
  rewrite Z2Nat.id in *; auto.
  assert (EE : 1 + Z.pred i' = i') by omega.
  rewrite EE in H8.
  rewrite H8 in H2. rewrite Hv'.
  congruence.
Qed.


Lemma fold_array_spec: forall gen_f gen_n m0 s0 a vs n f,
  (forall (Q: memory -> stack -> Prop),
  HT cblock gen_n
     (fun m s => exists ign0,
                   s = (ign0,handlerTag):::s0 /\ m = m0 /\
                   Q m ((n m0 s0,handlerTag):::(ign0,handlerTag):::s0))
     Q) ->
  (forall (Q: memory -> stack -> Prop),
  HT cblock gen_f
     (fun m s => exists x v ign0 ign1 ign2,
                   s = (x,handlerTag):::(v,handlerTag):::
                       (ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0 /\
                   m = m0 /\
                   Q m (((f m0 s0) x v,handlerTag):::
                        (ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0))
     Q) ->
  memarr m0 a vs ->
  Mem.stamp a = Kernel ->
  HT cblock
     (fold_array gen_n gen_f)
     (fun m s => s = (Vptr a 0,handlerTag):::s0 /\ m = m0)
     (fun m s => s = (fold_right (f m0 s0) (n m0 s0) vs,handlerTag):::s0 /\ m = m0).
Proof.
 intros.
 unfold fold_array.
 build_vc idtac.  (* builds some stupid glue steps *)
 eapply HT_weaken_conclusion.
 eapply (genRepeat_spec' _ (fold_array_body gen_f) (Ifab f n a vs m0 s0)).
 intros.
 eapply HT_consequence'.
 eapply (fab_spec gen_f f n a vs m0 s0 i H0).
 intros. destruct H4 as [s' [? ?]]. exists s'. intuition.
 intros. destruct H4 as [m' [s' [s'0 [? ?]]]].
 destruct H6 as [i' [v' [? [? [? [? [? ?]]]]]]].
 simpl in H5. destruct H5 as [s'' [? ?]].
 destruct H12 as [i0 [v0 [? [? [? [? [? ?]]]]]]]. subst. inv H10. inv H16.
 eexists.  split. auto.  unfold Ifab.
 eexists (Zpred i').
 eexists.
 split; eauto.
 simpl. intros.
 destruct H3 as [s' [? ?]].
 destruct H4 as [i' [ v' [? [? [? [? [? ?]]]]]]]. subst. inv H8.
 do 3 eexists. split; eauto.
 do 4 eexists. split; eauto.
 split; eauto.
 split; eauto.
 do 3 eexists. split; eauto.

 simpl. instantiate
          (1:= (fun m s => exists i s',
                             0 <= i /\ s = (Vint i, handlerTag) ::: s' /\ Ifab f n a vs m0 s0 m s)).
 auto.
 2: instantiate (1:= (fun m s => s = (Vptr a 0, handlerTag) ::: s0 /\ m = m0)); auto.

 inv H1.
 eapply HT_strengthen_premise.
 eapply H.
 split_vc.
 split; eauto.
 instantiate (1:= (Z.of_nat (length vs))).  omega.
 split.  eauto.
 unfold Ifab.
 split_vc.
 split. instantiate (1:= Z.of_nat(length vs)). omega.
 split. econstructor; eauto.
 split; eauto.
 split; eauto.
 rewrite dropZ_all.
 auto.
Qed.


Lemma fold_array_spec_wp: forall gen_f gen_n n f m0 s0 (Q: memory -> stack -> Prop),
  (forall (Q: memory -> stack -> Prop),
  HT cblock gen_n
     (fun m s => exists ign0,
                   s = (ign0,handlerTag):::s0 /\ m = m0 /\
                   Q m ((n m0 s0,handlerTag):::(ign0,handlerTag):::s0))
     Q) ->
  (forall (Q: memory -> stack -> Prop),
  HT cblock gen_f
     (fun m s => exists x v ign0 ign1 ign2,
                   s = (x,handlerTag):::(v,handlerTag):::
                       (ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0 /\
                   m = m0 /\
                   Q m (((f m0 s0) x v,handlerTag):::
                        (ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0))
     Q) ->
  HT cblock
     (fold_array gen_n gen_f)
     (fun m s => exists a vs,
                   memarr m0 a vs /\ Mem.stamp a = Kernel /\ s = (Vptr a 0,handlerTag):::s0 /\ m = m0 /\
                   Q m ((fold_right (f m0 s0) (n m0 s0) vs,handlerTag):::s0))
     Q.
Proof.
  intros.
  eapply HT_forall_exists. intro a.
  eapply HT_forall_exists. intro vs.
  eapply HT_fold_constant_premise.  intros.
  eapply HT_fold_constant_premise.  intros.
  eapply HT_consequence'. eapply fold_array_spec; eauto.
  split_vc.
  split_vc.
Qed.


(* Existsb. *)

(* Initial stack: a::S
   Final stack: r::S
        where gen_f assumes x::_::_::_::_::S and generates b::_::_::_::_::S with b the result of testing x
        and r = boolean: gen_f answers true on some element
*)
Definition exists_array gen_f :=  (* a S *)
      fold_array (                (* _ S *)
                    genFalse      (* 0 _ S *)
                 )                (* v _ S *)
                 (                (* x v _ _ _ S *)
                    gen_f         (* b v _ _ _ S *)
                 ++ genOr         (* b\/v _ _ _ S *)
                 )                (* v' _ _ _ S *)
.

Definition boolToVal (b : bool) : val := Vint (boolToZ b).

Lemma boolToVal_existsb : forall f xs,
                          boolToVal (existsb f xs) =
                          fold_right (fun x v : val => orv (boolToVal (f x)) v) (Vint 0) xs.
Proof.
  induction xs;  simpl; auto.
  destruct (f a); unfold orv in *; simpl; auto.
Qed.

Lemma exists_array_spec_wp : forall gen_f (f: memory -> stack -> val -> bool) s0 m0,
  (forall (Q: memory -> stack -> Prop),
  HT cblock gen_f
     (fun m s => exists x ign0 ign1 ign2 ign3,
                   s = (x,handlerTag):::
                       (ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::(ign3,handlerTag):::s0 /\
                   m = m0 /\
                   Q m ((boolToVal(f m0 s0 x),handlerTag):::
                        (ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::(ign3,handlerTag):::s0))
     Q) ->
  forall (Q: memory -> stack -> Prop),
  HT cblock (exists_array gen_f)
     (fun m s => exists a vs,
                      memarr m a vs /\
                      Mem.stamp a = Kernel /\
                      s = (Vptr a 0,handlerTag):::s0 /\
                      m = m0 /\
                      Q m ((boolToVal (existsb (f m s0) vs),handlerTag):::s0))
     Q.
Proof.
  intros.
  unfold exists_array.
  eapply HT_strengthen_premise.
  eapply fold_array_spec_wp with
           (n:= fun _ _ => boolToVal false)
           (f:= fun m0 s0 x v => orv (boolToVal (f m0 s0 x)) v); eauto.
  - intro. eapply HT_strengthen_premise. eapply genFalse_spec_wp.
    split_vc.
  - intro.
    eapply HT_compose_flip.
    eapply genOr_spec_general_wp; eauto.
    eapply HT_strengthen_premise.
    eapply H.
    split_vc.
  - split_vc. rewrite boolToVal_existsb in H3.  auto.
Qed.

(* Forallb. *)

(* Initial stack: a::S
   Final stack: r::S
        where gen_f assumes x::_::_::_::_::S and generates b::_::_::_::_::S with b the result of testing x
        and r = boolean: gen_f answers true on all elements
*)

Definition forall_array gen_f :=  (* a S *)
      fold_array (                (* _ S *)
                    genTrue       (* 1 _ S *)
                 )                (* v _ S *)
                 (                (* x v _ _ _ S *)
                    gen_f         (* b v _ _ _ S *)
                 ++ genAnd        (* b/\v _ _ _ S *)
                 )                (* v' _ _ _ S *)
.

Lemma boolToVal_forallb : forall f xs, boolToVal (forallb f xs) =
                                       fold_right (fun x v : val => andv (boolToVal (f x)) v) (Vint 1) xs.
Proof.
  induction xs;  simpl; auto.
  destruct (f a); unfold andv in *; simpl; auto.
Qed.

Lemma forall_array_spec_wp : forall gen_f (f: memory -> stack -> val -> bool) s0 m0,
  (forall (Q: memory -> stack -> Prop),
  HT cblock gen_f
     (fun m s => exists x ign0 ign1 ign2 ign3,
                   s = (x,handlerTag):::
                       (ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::(ign3,handlerTag):::s0 /\
                   m = m0 /\
                   Q m ((boolToVal(f m0 s0 x),handlerTag):::
                       (ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::(ign3,handlerTag):::s0))
     Q) ->
  forall (Q: memory -> stack -> Prop),
  HT cblock (forall_array gen_f)
     (fun m s => exists a vs,
                      memarr m a vs /\
                      Mem.stamp a = Kernel /\
                      s = (Vptr a 0,handlerTag):::s0 /\
                      m = m0 /\
                      Q m ((boolToVal (forallb (f m s0) vs),handlerTag):::s0))
     Q.
Proof.
  intros.
  unfold forall_array.
  eapply HT_strengthen_premise.
  eapply fold_array_spec_wp with
           (n:= fun _ _ => boolToVal true)
           (f:= fun m0 s0 x v => andv (boolToVal (f m0 s0 x)) v); eauto.
  - intro. eapply HT_strengthen_premise; try eapply genTrue_spec_wp.
    split_vc.
  - intro.
    eapply HT_compose_flip.
    eapply genAnd_spec_general_wp; eauto.
    eapply HT_strengthen_premise; solve [split_vc].
  - split_vc. rewrite boolToVal_forallb in H3. auto.
Qed.

(* In_array *)

(* Initial stack:  a::x::_
   Final stack:    r::_
      where r = boolean: x is in array a. *)

Definition in_array :=           (* a x *)
      exists_array (             (* y _ _ _ _ x *)
                       [Dup 5]   (* x y _ _ _ _ x *)
                   ++  genEq     (* x=y _ _ _ _ x *)
                   )             (* r x *)
   ++ [Swap 1]                   (* x r *)
   ++ pop                        (* r *)
.

Definition val_list_in_b (x: val) (xs:list val) : bool :=
  existsb (fun x' => if EquivDec.equiv_dec x x' then true else false) xs.

Lemma in_array_spec: forall a vs x s0 m0,
  memarr m0 a vs ->
  HT cblock
    in_array
    (fun m s => s = (Vptr a 0,handlerTag):::(x,handlerTag):::s0 /\ Mem.stamp a = Kernel /\ m = m0)
    (fun m s => s = (boolToVal(val_list_in_b x vs),handlerTag):::s0 /\ m = m0)
.
Proof.
  intros. unfold in_array.
  eapply HT_strengthen_premise.
  - eapply HT_compose_flip.
    + build_vc idtac.
    + eapply exists_array_spec_wp with (f := fun _ _ y => if EquivDec.equiv_dec x y then true else false)
                                       (s0 := (x,handlerTag):::s0).
      intros.
      eapply HT_compose_flip; try eauto using genEq_spec_wp.
      eapply HT_strengthen_premise; try eapply dup_spec_wp.
      split_vc.
      unfold val_eq.
      destruct (EquivDec.equiv_dec x x0); assumption.
  - split_vc.
Qed.

Lemma in_array_spec_wp : forall (Q: memory -> stack -> Prop),
  HT cblock
    in_array
    (fun m s => exists a vs x s0 m0,
                  memarr m0 a vs /\
                  s = (Vptr a 0,handlerTag):::(x,handlerTag):::s0 /\
                  Mem.stamp a = Kernel /\
                  m = m0 /\
                  Q m0 ((boolToVal(val_list_in_b x vs),handlerTag):::s0))
    Q.
Proof.
  intros.
  eapply HT_forall_exists. intro a.
  eapply HT_forall_exists. intro vs.
  eapply HT_forall_exists. intro x.
  eapply HT_forall_exists. intro s0.
  eapply HT_forall_exists. intro m0.
  eapply HT_fold_constant_premise. intro.
  eapply HT_consequence'. eapply in_array_spec; eauto.
  simpl. intros. intuition jauto.
  simpl. intros. destruct H0 as [m' [s' [? [? [? ?]]]]]. destruct H1. subst. auto.
Qed.


(* Subset_arrays *)

(* Initial stack:  a1::a2::_.
   Final_stack:    r::_.
      where r = boolean: all elements of a1 are in a2
*)
Definition subset_arrays :=      (* a1 a2 *)
    forall_array (               (* x1 _ _ _ _ a2 *)
                    [Dup 5]      (* a2 x1 _ _ _ _ a2 *)
                 ++ in_array     (* x1ina2 _ _ _ _ a2 *)
                 )               (* r a2 *)
 ++ [Swap 1]                     (* a2 r *)
 ++ pop                          (* r *)
.


Definition val_list_subset_b (xs1 xs2:list val) : bool :=
  forallb (fun x1 => val_list_in_b x1 xs2) xs1.

Lemma subset_arrays_spec : forall a1 a2 vs1 vs2 s0 m0,
  memarr m0 a1 vs1 ->
  memarr m0 a2 vs2 ->
  Mem.stamp a1 = Kernel ->
  Mem.stamp a2 = Kernel ->
  HT cblock subset_arrays
     (fun m s => s = (Vptr a1 0,handlerTag):::(Vptr a2 0,handlerTag):::s0 /\
                 m = m0)
     (fun m s => s = ((boolToVal (val_list_subset_b vs1 vs2),handlerTag):::s0) /\ m = m0).
Proof.
  intros. unfold subset_arrays.
  eapply HT_compose_flip; try solve [build_vc idtac].
  eapply HT_strengthen_premise.
  - eapply forall_array_spec_wp with (f := fun _ s0 y => val_list_in_b y vs2) (s0 := (Vptr a2 0,handlerTag):::s0).
    intros.
    eapply HT_compose_flip; try eapply in_array_spec_wp.
    eapply HT_strengthen_premise; try eapply dup_spec_wp.
    split_vc.
  - clear H0. split_vc.
Qed.

Lemma subset_arrays_spec_wp : forall (Q: memory -> stack -> Prop),
  HT cblock
    subset_arrays
    (fun m s => exists a1 a2 vs1 vs2 s0 m0,
                  memarr m0 a1 vs1 /\
                  memarr m0 a2 vs2 /\
                  Mem.stamp a1 = Kernel /\ Mem.stamp a2 = Kernel /\
                  s = (Vptr a1 0,handlerTag):::(Vptr a2 0,handlerTag):::s0 /\
                  m = m0 /\
                  Q m0 ((Vint (boolToZ(val_list_subset_b vs1 vs2)),handlerTag):::s0))
    Q.
Proof.
  intros.
  eapply HT_forall_exists. intro a1.
  eapply HT_forall_exists. intro a2.
  eapply HT_forall_exists. intro vs1.
  eapply HT_forall_exists. intro vs2.
  eapply HT_forall_exists. intro s0.
  eapply HT_forall_exists. intro m0.
  eapply HT_fold_constant_premise. intro.
  eapply HT_fold_constant_premise. intro.
  eapply HT_fold_constant_premise. intro.
  eapply HT_fold_constant_premise. intro.
  eapply HT_consequence'. eapply subset_arrays_spec with (a1:=a1) (a2:=a2); eauto.
  simpl. intros. intuition jauto.
  simpl. intros. destruct H3 as [m' [s' [? [? ?]]]]. intuition. subst. auto.
Qed.

(* Extend array *)

(* Initial stack:   a::x::_
   Final stack:     r::_
          where r is a fresh array containing the contents of a followed by x
   Side effects: allocates and fills the fresh array *)

Definition extend_array :=   (* a x *)
     [Dup 0]                 (* a a x *)
  ++ [Load]                  (* l a x *)
  ++ [Push 1]                (* 1 l a x *)
  ++ [Add]                   (* l+1 a x *)
  ++ alloc_array             (* r a x *)
  ++ [Dup 1]                 (* a r a x *)
  ++ [Load]                  (* l r a x *)
  ++ copy                    (* 0 r a x *)
  ++ pop                     (* r a x *)
  ++ [Dup 0]                 (* r r a x *)
  ++ [Swap 2]                (* a r r x *)
  ++ [Load]                  (* l r r x *)
  ++ [Push 1]                (* 1 l r r x *)
  ++ [Add]                   (* l+1 r r x *)
  ++ [Add]                   (* r+l+1 r x *)
  ++ [Swap 1]                (* r r+l+1 x *)
  ++ [Swap 2]                (* x r+l+1 r *)
  ++ [Swap 1]                (* r+l+1 x r *)
  ++ [Store]                 (* r *)
.


Lemma extend_array_spec_wp : forall (Q : memory -> stack -> Prop),
  HT cblock
   extend_array
   (fun m s => exists a vs x s0,
                 s = (Vptr a 0,handlerTag):::(x,handlerTag):::s0 /\
                 memarr m a vs /\
                 Mem.stamp a = Kernel /\
                 (forall r m1,
                    extends m m1 ->
                    Mem.get_frame m r = None ->
                    memarr m1 r (vs++[x]) ->
                    Q m1 ((Vptr r 0,handlerTag):::s0)))
   Q.

Proof.
  intros. unfold extend_array.

  build_vc ltac:(try apply copy_spec_wp; try apply alloc_array_spec_wp). auto.

  intros m ? (a & vs & x & s & ? & ARR & STAMPa & POST). subst.
  destruct ARR. subst.
  simpl.
  eexists. split; eauto.
  do 4 eexists.
  do 3 (split; eauto).
  do 4 eexists.
  do 2 (split; try reflexivity).
  do 2 eexists.
  do 2 (split; try reflexivity; try omega).
  intros b m' EXT VALID LOAD' FRESH STAMPb.
  assert (NEQab : a <> b).
  { intros contra. subst. unfold load in LOAD.
    destruct (Mem.get_frame m b); congruence. }
  eexists. split; try reflexivity.
  assert (LOAD'' := extends_load _ _ _ _ _ EXT LOAD).
  do 4 eexists.
  do 3 (split; eauto).
  do 6 eexists.
  split.
  2: split; eauto. omega.
  split.
  { intros.
    eapply extends_valid_address; eauto.
    eapply memseq_valid; eauto. omega. }
  split.
  { intros. apply VALID. omega. }
  split; try congruence.
  do 2 (split; auto).
  intros m'' (COPY & EQLOAD & EQFRAME).
  simpl in COPY.
  assert (EQFRAME' : forall b' off, b' <> b -> load b' off m'' = load b' off m').
  { unfold load.
    intros.
    rewrite EQFRAME; eauto. }
  do 3 eexists.
  split; eauto.
  simpl.
  eexists. split; eauto.
  do 4 eexists. do 3 (split; eauto).
  do 4 eexists.
  do 3 (split; eauto).
  { rewrite EQFRAME'; eauto. }
  do 4 eexists. do 2 (split; try reflexivity).
  do 4 eexists. do 2 (split; try reflexivity).
  do 4 eexists. do 3 (split; eauto).
  do 4 eexists. do 3 (split; eauto).
  do 4 eexists. do 3 (split; eauto).
  assert (STORE : valid_address b (1 + Z.of_nat (length vs) + 0) m'').
  { unfold valid_address.
    rewrite EQLOAD; try omega.
    apply VALID. omega. }
  eapply valid_store in STORE. destruct STORE as [m''' STORE].
  do 6 eexists. split; [|split; eauto]; eauto.
  split; eauto.
  apply POST; eauto.
  - intros b' fr' FRAME.
    assert (b' <> b) by congruence.
    erewrite (get_frame_store_neq _ _ _ _ _ _ _ _ STORE); eauto.
    rewrite EQFRAME; eauto.
  - econstructor; eauto.
    + erewrite load_store_old; eauto.
      * rewrite EQLOAD; try omega.
        rewrite LOAD'.
        repeat f_equal.
        rewrite app_length.
        simpl (length [x]).
        zify. ring.
      * intros contra.
        assert (0 = 1 + Z.of_nat (length vs) + 0) by congruence.
        omega.
    + apply memseq_app with (vs1 := vs) (vs2 := [x]).
      split.
      * eapply memseq_eq with (m1 := m); eauto.
        intros z RANGE.
        { rewrite (load_store_old STORE); eauto.
          - rewrite <- COPY; try omega.
            rewrite EQFRAME'; try congruence.
            unfold load in LOAD.
            unfold load.
            destruct (Mem.get_frame m a) as [fr|] eqn:FRAME; try congruence.
            apply EXT in FRAME.
            rewrite FRAME.
            reflexivity.
          - intros contra.
            assert (1 + z = 1 + Z.of_nat (length vs) + 0) by congruence.
            omega. }
      * constructor; try solve [constructor].
        replace (1 + Z.of_nat (length vs) + 0) with (1 + Z.of_nat (length vs)) in STORE by ring.
        erewrite load_store_new; eauto.
Qed.

End with_hints.

End with_cblock.
