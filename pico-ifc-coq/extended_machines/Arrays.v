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
Require Import Coq.Arith.Compare_dec.

(* Everything to do with machine execution and triples has to be parameterized over SysTable. *)
Section with_cblock.

Variable cblock : block privilege.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.
Variable table : CSysTable.

Local Notation val := (val privilege).
Local Notation Atom := (Atom val privilege).
Local Notation memory := (Mem.t Atom privilege).
Local Notation PcAtom := (PcAtom val).
Local Notation block := (block privilege).

Fixpoint narrow (n : nat) (A B : Type) : Type :=
  match n with
    | O => B
    | S n' => A -> narrow n' A B
  end.

Fixpoint nexists {n : nat} {A : Type}
                 (P : narrow n A Prop) : Prop :=
  match n return narrow n A Prop -> Prop with
    | O => fun P => P
    | S n' => fun P => exists a, nexists (P a)
  end P.

Fixpoint stk_env_aux
           (e : list val) (s0 : list CStkElmt)
           (k : list CStkElmt -> Prop) : narrow (length e) val Prop :=
  match e with
    | nil => k s0
    | v :: e' => fun t => stk_env_aux e' s0 (fun r => k ((v,t):::r))
  end.

Definition stk_env (s : list CStkElmt) (e : list val)
                   (s0 : list CStkElmt) : Prop :=
  Eval compute in
    nexists (stk_env_aux e s0 (fun r => s = r)).

Ltac apply_wp :=
  try unfold pop, nop, push, dup, swap;
  match goal with
  | |- HT _ _ [Store] _ _ => eapply store_spec
  | |- HT _ _ [Add] _ _  => eapply add_spec
  | |- HT _ _ [Dup ?N] _ _ => eapply dup_spec
  | |- HT _ _ [Swap ?N] _ _ => eapply swap_spec
  | |- HT _ _ [Load] _ _ => eapply load_spec
  | |- HT _ _ [Push ?N] _ _ => eapply push_spec
  | |- HT _ _ [Pop] _ _ => eapply pop_spec
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
Hint Resolve extends_update.

(* Memory copy.  *)

(* Initial stack:  count :: dst0 :: src0 :: _
   Final stack:    0 :: dst0 :: src0 :: _
   Side Effects: copies (src0,src0+count] to (dst0,dst0+count]  (provided these regions are disjoint) *)

Definition copy :=
  genFor ([Dup 2] ++ (* src0 :: count :: dst0 :: src0 :: _ *)
          [Dup 1] ++ (* count :: src0 :: count :: dst0 :: src0 :: _ *)
          [Add] ++   (* src0+count :: count :: dst0 :: src0 :: _ *)
          [Load] ++  (* mem[src0+count] :: count :: dst0 :: src0 :: _ *)
          [Dup 2] ++ (* dst0 :: mem[src0+count] :: count :: dst0 :: src0 :: _ *)
          [Dup 2] ++ (* count :: dst0 :: mem[src0+count] :: count :: dst0 :: src0 :: _ *)
          [Add] ++   (* dst0+count :: mem[src0+count] :: count :: dst0 :: src0 :: _ *)
          [Store]).

(* The loop invariant for copy. *)
Definition Icopy (sz cnt:Z) bdst odst bsrc osrc (m0 : memory) s0 :=
  fun m s =>
    exists t2 t3,
      s = (Vptr (bdst, odst),t2):::(Vptr (bsrc, osrc),t3):::s0 /\
      (cnt <= sz) /\
      (forall z, osrc < z <= osrc+cnt -> valid_address (bsrc, z) m) /\
      (forall z, odst < z <= odst+cnt -> valid_address (bdst, z) m) /\
      (bdst <> bsrc) /\
      (Mem.stamp bdst = Kernel) /\
      (Mem.stamp bsrc = Kernel) /\
      (forall z, cnt < z <= sz -> load (bsrc,osrc+z) m = load (bdst,odst+z) m) /\
      (forall z, ~ (odst+cnt < z <= odst+sz) -> load (bdst,z) m = load (bdst,z) m0) /\
      (forall b, b <> bdst -> Mem.get_frame m b = Mem.get_frame m0 b).

Lemma copy_spec : forall (Q : memory -> stack -> Prop),
  HT cblock table copy
  (fun m s => exists sz bdst odst bsrc osrc s0 t1 t2 t3,
                0 <= sz /\
                s = (Vint sz,t1):::(Vptr (bdst,odst),t2):::(Vptr (bsrc,osrc),t3):::s0 /\
                (forall z, osrc < z <= osrc+sz -> valid_address (bsrc,z) m) /\
                (forall z, odst < z <= odst+sz -> valid_address (bdst,z) m) /\
                (bdst <> bsrc) /\
                Mem.stamp bdst = Kernel /\
                Mem.stamp bsrc = Kernel /\
                (forall m1 t1' t2' t3',
                   (forall z, 0 < z <= sz -> load (bsrc,osrc+z) m1 = load (bdst,odst+z) m1) /\
                   (forall z, ~ (odst < z <= odst+sz) -> load (bdst,z) m1 = load (bdst,z) m) /\
                   (forall b, b <> bdst -> Mem.get_frame m1 b = Mem.get_frame m b) ->
                   Q m1 ((Vint 0,t1'):::(Vptr (bdst,odst),t2'):::(Vptr (bsrc,osrc),t3'):::s0)))
  Q.
Proof.
  intros. unfold copy.
  eapply HT_strengthen_premise with
  (fun m s => exists sz bdst odst bsrc osrc s0 m0 t1 t2 t3,
                0 <= sz /\
                m = m0 /\
                s = (Vint sz,t1):::(Vptr (bdst,odst),t2):::(Vptr (bsrc,osrc),t3):::s0 /\
                (forall z, osrc < z <= osrc+sz -> valid_address (bsrc,z) m) /\
                (forall z, odst < z <= odst+sz -> valid_address (bdst,z) m) /\
                (bdst <> bsrc) /\
                Mem.stamp bdst = Kernel /\
                Mem.stamp bsrc = Kernel /\
                (forall m1 t1' t2' t3',
                   (forall z, 0 < z <= sz -> load (bsrc,osrc+z) m1 = load (bdst,odst+z) m1) /\
                   (forall z, ~ (odst < z <= odst+sz) -> load (bdst,z) m1 = load (bdst,z) m) /\
                   (forall b, b <> bdst -> Mem.get_frame m1 b = Mem.get_frame m b) ->
                   Q m1 ((Vint 0,t1'):::(Vptr (bdst,odst),t2'):::(Vptr (bsrc,osrc),t3'):::s0)));
    [|solve [split_vc]].
  eapply HT_forall_exists. intro sz.
  eapply HT_forall_exists. intro bdst.
  eapply HT_forall_exists. intro odst.
  eapply HT_forall_exists. intro bsrc.
  eapply HT_forall_exists. intro osrc.
  eapply HT_forall_exists. intro s0.
  eapply HT_forall_exists. intro m0.
  eapply HT_forall_exists. intro t1.
  eapply HT_forall_exists. intro t2.
  eapply HT_forall_exists. intro t3.
  eapply HT_fold_constant_premise; intro.
  eapply HT_strengthen_premise.
  { eapply genFor_spec
      with (I := fun (Q : _ -> _ -> Prop) m s i =>
                   Icopy sz i bdst odst bsrc osrc m0 s0 m s /\
                   forall m' s' ti',
                     Icopy sz 0 bdst odst bsrc osrc m0 s0 m' s' ->
                     Q m' ((Vint 0, ti') ::: s')).
    { intros i POS.
      eexists. split.
      - build_vc idtac. trivial.
      - intros m s t (INV & END).
        unfold Icopy in *.
        destruct INV as (t5 & t6 & Hs & ? & VALIDSRC & VALIDDST & ? & ? & ? & COPY & REST & ?).
        subst.
        exploit (VALIDSRC (i + osrc)); try omega. intros [val Hval].
        exploit (VALIDDST (i + odst)); try omega. intros [val' Hval'].
        eapply load_some_store_some in Hval'. destruct Hval' as [m' Hm'].
        split_vc.
        split; [|split; eauto]; eauto.
        split_vc.
        split.
        { split_vc.
          repeat split; eauto; try omega.
          + intros.
            eapply valid_address_upd; eauto.
            eapply VALIDSRC. omega.
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
            erewrite (get_frame_store_neq _ _ _ _ _ _ _ _ Hm'); eauto. }
        intros. split_vc. apply END.
        do 2 eexists. repeat (split; eauto). }

    intros m s t (END & POST). eauto. }

  unfold Icopy. split_vc. split.
  - split_vc. repeat split; intros; omega.
  - split_vc.
    replace (odst + 0) with odst in * by ring. eauto.
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
| memseq_cons : forall z v t vs, load (b,z) m = Some (v, t) -> memseq m b (z+1) vs -> memseq m b z (v::vs)
.

Lemma memseq_valid : forall m b a vs,
  memseq m b a vs ->
  forall z, a <= z < a + Z.of_nat(length vs) -> valid_address (b,z) m.
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
  forall z, a <= z < a + Z.of_nat(length vs) -> exists v t, load (b,z) m = Some(v,t).
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
                           load (b1,a1+z) m1 = load (b2,a2+z) m2)
         (SEQ : memseq m1 b1 a1 vs),
    memseq m2 b2 a2 vs.
Proof.
  intros.
  generalize dependent a2.
  induction SEQ.
  - intros. constructor.
  - intros.
    assert (Hz : load (b1,z) m1 = load (b2,a2) m2).
    { replace z with (z+0) by ring. replace a2 with (a2+0) by ring.
      eapply LOAD. simpl. zify; omega. }
    destruct (load (b2,a2) m2) as [[v0 l0]|] eqn:E; try congruence.
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
| memarr_i : forall c t
                    (LOAD : load (b,0) m = Some (Vint (Z_of_nat c), t))
                    (SEQ : memseq m b 1 vs)
                    (LEN : c = length vs),
               memarr m b vs.

(* Array allocation.  *)

(* Initial stack: count :: _
   Final stack:  ptr-to-array :: _
   Side effects: allocates fresh array of size count *)

Definition alloc_array:= push 0 ++ [Dup 1] ++ push 1 ++ [Add] ++ [Alloc] ++ dup ++ [Swap 2] ++ [Swap 1] ++ [Store].

Lemma alloc_array_spec: forall (Q : memory -> stack -> Prop),
  HT cblock table alloc_array
     (fun m s => exists cnt t s0,
                   s = (Vint cnt,t):::s0 /\
                   cnt >= 0 /\
                   (forall b m1 t2,
                      extends m m1 ->
                      (forall p, 0 < p <= cnt -> valid_address (b,p) m1) ->
                      (exists t1, load (b,0) m1 = Some (Vint cnt, t1)) ->
                      Mem.get_frame m b = None ->
                      Mem.stamp b = Kernel ->
                      Q m1 ((Vptr (b,0),t2):::s0)))
     Q.
Proof.
  intros.
  unfold alloc_array.
  Opaque Z.add. (* not sure why this is necessary this time *)
  unfold alloc_array.
  build_vc ltac: (try apply alloc_spec; eauto).
  intros m s (cnt & t & s0 & ? & ? & H).
  subst. simpl.
  clear stamp_cblock.
  do 31 (try eexists; simpl; eauto); try omega.
  repeat (split; eauto).
  assert (VALID : valid_address (b,0) m0).
  { eexists (Vint 0, handlerTag).
    erewrite load_alloc; eauto.
    simpl.
    (* suffices for 8.4pl1:
    destruct (EquivDec.equiv_dec b b ). *)
    (* explicit arguments in following needed for 8.4 *)
    destruct(
       @EquivDec.equiv_dec _ _
         (@eq_equivalence (Memory.block privilege)) _ b b); try congruence.
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
        (* suffices for 8.4pl1:
        destruct (EquivDec.equiv_dec b b); try congruence. *)
        (* explicit arguments for 8.4 *)
        destruct (
           @EquivDec.equiv_dec _
              (@eq (Memory.block privilege)) _ _ b); try congruence.
        destruct (Z_le_dec 0 p); try omega.
        destruct (Z_lt_dec p (1 + cnt)); try omega.
        reflexivity.
      * intros contra.
        inv contra.
        omega.
    + eexists. eapply load_store_new; eauto.
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

Lemma sum_array_lengths_spec : forall Q : HProp,
  HT cblock table sum_array_lengths
     (fun m s => exists a1 a2 s0 l1 l2 t1 t2 t1' t2',
                 s = (Vptr (a2,0),t2):::(Vptr (a1,0),t1):::s0 /\
                 load (a2,0) m = Some (Vint l2, t1') /\
                 load (a1,0) m = Some (Vint l1, t2') /\
                 Mem.stamp a1 = Kernel /\
                 Mem.stamp a2 = Kernel /\
                 forall t1'' t2'',
                   Q m ((Vint (l2+l1),handlerTag):::(Vptr (a2,0),t2''):::(Vptr (a1,0),t1''):::s0))
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


Lemma concat_arrays_spec : forall (Q :memory -> stack -> Prop),
  HT cblock table
   concat_arrays
   (fun m s => exists a2 a1 vs1 vs2 s0 t1 t2,
                 s = (Vptr (a2,0),t2):::(Vptr (a1,0),t1):::s0 /\
                 memarr m a1 vs1 /\ memarr m a2 vs2 /\
                 Mem.stamp a1 = Kernel /\ Mem.stamp a2 = Kernel /\
                 (forall r m1 t,
                    extends m m1 ->
                    memarr m1 r (vs1 ++ vs2) ->
                    Mem.get_frame m r = None ->
                    Mem.stamp r = Kernel ->
                    Q m1 ((Vptr (r,0),t):::s0)))
   Q.
Proof.
  intros. unfold concat_arrays.

  build_vc ltac:(try apply copy_spec; try apply alloc_array_spec; try apply sum_array_lengths_spec).

  intros m s (a2 & a1 & vs1 & vs2 & t1 & t2 & s0 & ? & ARR1 & ARR2 & K1 & K2 & POST).
  destruct ARR1. destruct ARR2.
  split_vc'. intros t1'' t2''. split_vc'.
  intros b m1 t'' EXT VALID [t''' LOADSUM] FRESH KERNEL.
  assert (a1 <> b).
  { intros contra. subst. unfold load in *. simpl in *.
    rewrite FRESH in LOAD.
    congruence. }
  assert (a2 <> b).
  { intros contra. subst. unfold load in *. simpl in *.
    rewrite FRESH in LOAD0.
    congruence. }

  do 8 (try eexists); eauto.
  eexists (Vint (Z.of_nat (length vs1)), t).
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
                       load (b', off) m0 = load (b', off) m1).
  { unfold load.
    intros.
    rewrite H3; trivial. }
  split.
  { assert (LOAD'' := LOAD).
    eapply extends_load with (m3 := m1) in LOAD''; eauto.
    cut (load (a1, 0) m0 = load (a1, 0) m1).
    { intros E. rewrite E. eassumption. }
    unfold load.
    rewrite H3; trivial. }
  split_vc.
  split.
  { assert (LOAD'' := LOAD0).
    eapply extends_load with (m3 := m1) in LOAD''; eauto.
    cut (load (a2, 0) m0 = load (a2, 0) m1).
    { intros E. rewrite E. eassumption. }
    unfold load.
    rewrite H3; trivial. }
  split_vc.
  split; try (split; try solve [eauto]); try omega.
  split.
  { simpl. intros.
    eapply memseq_valid with (z := z) in SEQ0; try omega.
    exploit @extends_valid_address; eauto.
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
        assert (VALID' : valid_address (a1,1 + z) m).
        { eapply memseq_valid; eauto. omega. }
        destruct VALID' as [a VALID'].
        rewrite VALID'.
        symmetry.
        eapply extends_load; eauto.
      * apply memseq_eq with (m1 := m) (b1 := a2) (a1 := 1); eauto.
        intros.
        replace (1 + Z.of_nat (length vs1) + z) with (Z.of_nat (length vs1) + 0 + (1 + z)) by ring.
        rewrite <- H4; try omega.
        assert (LOADm2m0 : load (a2,1 + z) m2 = load (a2,1 + z) m0).
        { unfold load. rewrite H6; trivial. }
        rewrite LOADm2m0.
        rewrite LOADm0m1; try congruence.
        assert (VALID' : valid_address (a2,1 + z) m).
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
  ++  genFor                             (* i v a S *)
        (fold_array_body gen_f)          (* i v' a S *)
  ++ pop                                 (* r a S *)
  ++ [Swap 1]                            (* a r S *)
  ++ pop                                 (* r S *)
.

(* Invariant for fold array body *)
Definition Ifab (f : val -> val -> val) (n: val)
                (a:block) (vs:list val) m0 s0 i :=
    fun m s =>
      exists v,
        i <= Z.of_nat (length vs) /\
        memarr m a vs /\
        Mem.stamp a = Kernel /\
        m = m0 /\
        stk_env s [v; Vptr (a,0)] s0 /\
        v = fold_right f n (dropZ i vs).

Lemma memseq_dropZ :
  forall ms b z p vs
         (SEQ : memseq ms b z vs)
         (POS : p >= 0),
    memseq ms b (z + p) (dropZ p vs).
Proof.
  intros.
  unfold dropZ.
  destruct (Z.ltb_spec0 p 0); try omega.
  replace (_ + p) with (z + Z.of_nat (Z.to_nat p)) by (rewrite Z2Nat.id; omega).
  auto using memseq_drop.
Qed.

Lemma memarr_load :
  forall m a vs i x t
         (ARR : memarr m a vs)
         (LOAD : load (a,i) m = Some (x,t))
         (BOUNDS : 0 < i <= Z.of_nat (length vs)),
    index_list_Z (Z.pred i) vs = Some x.
Proof.
  intros.
  destruct ARR.
  assert (SEQ' : memseq m a i (dropZ (Z.pred i) vs)).
  { assert (E : i = 1 + Z.pred i) by omega.
    rewrite E at 1. apply memseq_dropZ; trivial.
    omega. }
  rewrite index_list_Z_dropZ_zero; try omega.
  exploit (@dropZ_cons _ (Z.pred i) vs); try omega.
  intros (x' & H). rewrite H in *.
  rewrite <- Zsucc_pred in *.
  inv SEQ'.
  assert (x' = x) by congruence. subst.
  reflexivity.
Qed.

(* AAA: When we use a Hoare triple in the premise of a WP rule (such
as in fab_spec' below), using WP style is not very convenient.

Suppose for concreteness that we want to prove a rule for a
higher-order generator [macro] of the form

   macro_spec : forall c (Q : HProp),
                  Hc -> HT (macro c) P Q

where P is some expression involving Q, and Hc is some hypothesis that
states that some triple should be valid for c. (An example of this is
fab_spec.) After proving this, we use macro_spec for proving another
triple. If Hc is in WP form (i.e., something like (forall Q, HT c P'
Q), where P' depends on Q), more likely than not, there will be a
mismatch between P' and the precondition that is computed from Q when
applying other previously proven Hoare logic rules. This forces us to
apply HT_strengthen_premise explicitly to be able to prove the triple,
and then prove the additional implication forall m s, P' m s -> P'' m
s.

One partial solution is to quantify the precondition in Hc
existentially and supplying the postcondition we want as "input", as
in genFor_spec:

(* genFor_spec *)
(*      : forall (cblock : block) (table : CSysTable) *)
(*          (I : HProp -> CodeTriples.memory -> list CStkElmt -> Z -> Prop) *)
(*          (c : CodeTriples.code) (Q : HProp), *)
(*        (forall i : Z, *)
(*         i > 0 -> *)
(*         exists Pc, *)
(*         HT cblock table c Pc *)
(*           (fun (m : CodeTriples.memory) (s : CodeTriples.stack) => *)
(*            exists t s', s = (Vint i, t) ::: s' /\ I Q m s' (Z.pred i)) /\ *)
(*         (forall (m : CodeTriples.memory) (s : list CStkElmt) (t : val), *)
(*          I Q m s i -> Pc m ((Vint i, t) ::: s))) -> *)
(*        (forall (m : CodeTriples.memory) (s : list CStkElmt) (t : val), *)
(*         I Q m s 0 -> Q m ((Vint 0, t) ::: s)) -> *)
(*        HT cblock table (genFor c) *)
(*          (fun (m : CodeTriples.memory) (s : CodeTriples.stack) => *)
(*           exists i t s', s = (Vint i, t) ::: s' /\ i >= 0 /\ I Q m s' i) Q *)

A good rule-of-thumb seems to be: triples in conclusions map an
arbitrary postcondition to a precondition that validates the
triple. In hypotheses, however, we instead suply the postcondition we
need as input and let the other rules we've proved before figure out
what the precondition should be.
*)

Definition fab_spec :
  forall gen_f f n m0 s0
         (HTf : forall (Q : memory -> stack -> Prop),
                  HT cblock table gen_f
                     (fun m s =>
                        exists x v i0 i1 i2,
                          stk_env s [x; v; i0; i1; i2] s0 /\
                          m = m0 /\
                          forall s',
                            stk_env s' [f x v; i0; i1; i2] s0 ->
                            Q m s')
                     Q)
         (Q : memory -> stack -> Prop),
    HT cblock table (fold_array_body gen_f)
       (fun m s =>
          exists i a vs s',
            stk_env s [Vint i] s' /\
            i > 0 /\
            Ifab f n a vs m0 s0 i m s' /\
            forall s'' s''',
              stk_env s'' [Vint i] s''' ->
              Ifab f n a vs m0 s0 (Z.pred i) m s''' ->
              Q m s'')
       Q.
Proof.
  intros.
  unfold fold_array_body.
  eapply HT_strengthen_premise.
  { repeat (eapply HT_compose; [eapply dup_spec|]).
    eapply HT_compose; try eapply add_spec.
    eapply HT_compose; try eapply load_spec.
    eapply HT_compose; try eapply HTf.
    eapply HT_compose; try eapply swap_spec.
    apply pop_spec. }
  clear.
  intros m ? (i & a & vs & s' & (ti & ?) & POS & INV & POST). subst.
  destruct INV as (v & BOUNDS & ARR & STAMP & ? & (tv & ta & ?) & ?).
  subst m0. subst. simpl.
  do 3 (eexists; split; eauto).
  do 6 eexists. split; eauto. simpl. split; eauto.
  assert (Hx : exists x tx, load (a,i) m = Some (x,tx)).
  { eapply memseq_read.
    destruct ARR. eauto. omega. }
  destruct Hx as (x & tx & Hx).
  do 4 eexists. split; eauto. simpl. split; trivial.
  replace (i + 0) with i by ring. split; eauto.
  do 5 eexists. split; [do 5 eexists; eauto|].
  split; trivial.
  intros s' (? & ? & ? & ? & ?). subst.
  do 4 eexists. do 3 (split; eauto).
  do 3 eexists. split; eauto.
  change (f x (fold_right f n (dropZ i vs))) with (fold_right f n (x :: dropZ i vs)).
  exploit (@dropZ_cons _ (Z.pred i) vs); try omega.
  intros (x' & H).
  rewrite <- Zsucc_pred in H.
  replace x' with x in *.
  { rewrite <- H. eapply POST.
    - eexists. eauto.
    - eexists. repeat split; eauto; try omega.
      do 2 eexists. reflexivity. }
  exploit memarr_load; eauto; try omega.
  intros H'.
  rewrite index_list_Z_dropZ_zero in H'; try omega.
  rewrite H in H'. compute in H'.
  congruence.
Qed.

Lemma fold_array_spec :
  forall gen_f gen_n n f m0 s0
         (HTn : forall (Q : memory -> stack -> Prop),
                  HT cblock table gen_n
                     (fun m s =>
                        exists i0,
                          stk_env s [i0] s0 /\
                          m = m0 /\
                          forall s',
                            stk_env s' [n; i0] s0 ->
                            Q m s')
                     Q)
         (HTf : forall (Q : memory -> stack -> Prop),
                  HT cblock table gen_f
                     (fun m s =>
                        exists x v i0 i1 i2,
                          stk_env s [x; v; i0; i1; i2] s0 /\
                          m = m0 /\
                          forall s',
                            stk_env s' [f x v; i0; i1; i2] s0 ->
                            Q m s')
                     Q)
         (Q : memory -> stack -> Prop),
    HT cblock table
       (fold_array gen_n gen_f)
       (fun m s => exists a vs,
                     memarr m a vs /\
                     Mem.stamp a = Kernel /\
                     stk_env s [Vptr (a, 0)] s0 /\
                     m = m0 /\
                     forall s',
                       stk_env s' [fold_right f n vs] s0 ->
                       Q m s')
       Q.
Proof.
  intros.
  unfold fold_array.
  eapply HT_strengthen_premise.

  (* Using PTs would remove the need for the things between the { }
     with no need for ad-hoc tactics. *)

  { eapply HT_compose; try eapply HTn.
    eapply HT_compose; try eapply dup_spec.
    eapply HT_compose; try eapply load_spec.
    eapply HT_compose; try eapply genFor_spec
                       with (I := fun (Q : HProp) m s i =>
                                    exists a vs,
                                      Ifab f n a vs m0 s0 i m s /\
                                      forall s' s'',
                                        stk_env s' [Vint 0] s'' ->
                                        Ifab f n a vs m0 s0 0 m s'' ->
                                        Q m s').
    { intros. eexists. split.
      - eapply fab_spec. apply HTf.
      - simpl.
        intros m s t (a & vs & INV & POST).
        do 4 eexists. split; [eexists; eauto|]. split; try omega.
        split; eauto.
        intros s'' s''' (? & ?) INV'. subst.
        do 2 eexists. split; eauto. }

    { intros m s t (a & vs & INV & POST). eapply POST; eauto. eexists. eauto. }
    eapply HT_compose; try eapply pop_spec.
    eapply HT_compose; try eapply swap_spec.
    eapply pop_spec. }

  intros m s (a & vs & ARR & KERNEL & ? & ? & POST).
  subst. simpl.
  eexists. do 2 (split; eauto).
  intros s' (? & ? & ?). subst.
  destruct ARR as [c ? LOAD SEQ ?]. subst.
  eexists. split; eauto.
  do 4 eexists. do 3 (split; eauto).
  do 3 eexists. split; eauto. split; try omega.
  do 2 eexists.
  split.
  { unfold Ifab.
    eexists.
    repeat split; eauto; try solve [econstructor; eauto]; try omega.
    rewrite dropZ_all. do 2 eexists. reflexivity. }
  clear - POST.
  intros s' s'' (? & ?) (? & _ & ARR & KERNEL & _ & (? & ? & ?) & ?). subst.
  do 3 eexists. split; eauto.
  do 4 eexists. do 3 (split; eauto).
  do 3 eexists. split; eauto.
  apply POST.
  eexists. reflexivity.
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

Lemma exists_array_spec : forall gen_f (f: val -> bool) s0 m0,
  (forall (Q: memory -> stack -> Prop),
  HT cblock table gen_f
     (fun m s => exists x i0 i1 i2 i3,
                   stk_env s [x; i0; i1; i2; i3] s0 /\
                   m = m0 /\
                   forall s',
                     stk_env s' [boolToVal (f x); i0; i1; i2; i3] s0 ->
                     Q m s')
     Q) ->
  forall (Q: memory -> stack -> Prop),
  HT cblock table (exists_array gen_f)
     (fun m s => exists a vs,
                      memarr m a vs /\
                      Mem.stamp a = Kernel /\
                      stk_env s [Vptr (a, 0)] s0 /\
                      m = m0 /\
                      forall s',
                        stk_env s' [boolToVal (existsb f vs)] s0 ->
                        Q m s')
     Q.
Proof.
  intros.
  unfold exists_array.
  eapply HT_strengthen_premise.
  { eapply fold_array_spec with
           (n:= boolToVal false)
           (f:= fun x v => orv (boolToVal (f x)) v); eauto.
    - clear Q. intros Q.
      eapply HT_strengthen_premise. eapply genFalse_spec.
      intros m s (i0 & (? & ?) & ? & POST).
      subst s.
      apply POST.
      do 2 eexists. reflexivity.
    - clear Q. intro Q.
      eapply HT_compose_flip; try eapply genOr_spec; eauto.
      eapply HT_strengthen_premise.
      eapply H.
      intros m s (x & v & i0 & i1 & i2 & E & ? & POST).
      do 5 eexists. split; eauto. split; eauto.
      intros s' (? & ? & ? & ? & ? & ?). subst.
      do 5 eexists. split; eauto.
      intros.
      eapply POST.
      do 4 eexists. eauto. }

  - unfold stk_env. split_vc.
    rewrite <- boolToVal_existsb. eauto.
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

Lemma forall_array_spec : forall gen_f (f: val -> bool) s0 m0,
  (forall (Q: memory -> stack -> Prop),
  HT cblock table gen_f
     (fun m s => exists x i0 i1 i2 i3,
                   stk_env s [x; i0; i1; i2; i3] s0 /\
                   m = m0 /\
                   forall s',
                     stk_env s' [boolToVal (f x); i0; i1; i2; i3] s0 ->
                     Q m s')
     Q) ->
  forall (Q: memory -> stack -> Prop),
  HT cblock table (forall_array gen_f)
     (fun m s => exists a vs,
                      memarr m a vs /\
                      Mem.stamp a = Kernel /\
                      stk_env s [Vptr (a, 0)] s0 /\
                      m = m0 /\
                      forall s',
                        stk_env s' [boolToVal (forallb f vs)] s0 ->
                        Q m s')
     Q.
Proof.
  intros.
  unfold exists_array.
  eapply HT_strengthen_premise.
  { eapply fold_array_spec with
           (n:= boolToVal true)
           (f:= fun x v => andv (boolToVal (f x)) v); eauto.
    - clear Q. intros Q.
      eapply HT_strengthen_premise. eapply genFalse_spec.
      intros m s (i0 & (? & ?) & ? & POST).
      subst s.
      apply POST.
      do 2 eexists. reflexivity.
    - clear Q. intro Q.
      eapply HT_compose_flip; try eapply genAnd_spec; eauto.
      eapply HT_strengthen_premise.
      eapply H.
      intros m s (x & v & i0 & i1 & i2 & E & ? & POST).
      do 5 eexists. split; eauto. split; eauto.
      intros s' (? & ? & ? & ? & ? & ?). subst.
      do 5 eexists. split; eauto.
      intros.
      eapply POST.
      do 4 eexists. eauto. }

  - unfold stk_env. split_vc.
    rewrite <- boolToVal_forallb. eauto.
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

Lemma in_array_spec : forall (Q: memory -> stack -> Prop),
  HT cblock table
    in_array
    (fun m s => exists a vs x t1 t2 s0 m0,
                  memarr m0 a vs /\
                  s = (Vptr (a, 0),t1):::(x,t2):::s0 /\
                  Mem.stamp a = Kernel /\
                  m = m0 /\
                  forall t,
                    Q m0 ((boolToVal(val_list_in_b x vs),t):::s0))
    Q.
Proof.
  intros. unfold in_array.
  eapply HT_forall_exists. intro a.
  eapply HT_forall_exists. intro vs.
  eapply HT_forall_exists. intro x.
  eapply HT_forall_exists. intro t1.
  eapply HT_forall_exists. intro t2.
  eapply HT_forall_exists. intro s0.
  eapply HT_forall_exists. intro m0.
  eapply HT_strengthen_premise.
  { eapply HT_compose; try eapply exists_array_spec with
                         (f := fun y => if EquivDec.equiv_dec x y then true else false)
                         (s0 := (x,t2):::s0).
    { clear Q. intros Q.
      eapply HT_strengthen_premise.
      { eapply HT_compose; try eapply dup_spec.
        eapply genEq_spec. }
      intros m s (? & ? & ? & ? & ? & (? & ? & ? & ? & ? & ?) & ? & POST).
      subst s. simpl.
      eexists. split; eauto.
      do 5 eexists. split; eauto.
      eapply POST.
      do 5 eexists.
      unfold val_eq.
      destruct (EquivDec.equiv_dec x x0); eauto. }

    eapply HT_compose; try eapply swap_spec.
    eapply pop_spec. }

  intros m s (? & ? & ? & ? & POST). subst.
  unfold stk_env.
  split_vc.
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

Lemma subset_arrays_spec : forall (Q: memory -> stack -> Prop),
  HT cblock table
    subset_arrays
    (fun m s => exists a1 a2 vs1 vs2 t1 t2 s0 m0,
                  memarr m0 a1 vs1 /\
                  memarr m0 a2 vs2 /\
                  Mem.stamp a1 = Kernel /\ Mem.stamp a2 = Kernel /\
                  s = (Vptr (a1, 0),t1):::(Vptr (a2, 0),t2):::s0 /\
                  m = m0 /\
                  forall t,
                    Q m0 ((Vint (boolToZ(val_list_subset_b vs1 vs2)),t):::s0))
    Q.
Proof.
  intros. unfold subset_arrays.
  eapply HT_forall_exists. intro a1.
  eapply HT_forall_exists. intro a2.
  eapply HT_forall_exists. intro vs1.
  eapply HT_forall_exists. intro vs2.
  eapply HT_forall_exists. intro t1.
  eapply HT_forall_exists. intro t2.
  eapply HT_forall_exists. intro s0.
  eapply HT_forall_exists. intro m0.
  eapply HT_fold_constant_premise. intro.
  eapply HT_fold_constant_premise. intro.
  eapply HT_fold_constant_premise. intro.
  eapply HT_fold_constant_premise. intro.
  eapply HT_strengthen_premise.
  { eapply HT_compose; try eapply forall_array_spec with
                           (f := fun y => val_list_in_b y vs2)
                           (s0 := (Vptr (a2, 0), t2) ::: s0).
    { clear Q. intros Q.
      eapply HT_strengthen_premise.
      { eapply HT_compose; try eapply dup_spec.
        eapply in_array_spec. }
      intros m s (x & ? & ? & ? & ? & (? & ? & ? & ? & ? & ?) & ? & POST).
      subst s. simpl.
      eexists. split; eauto.
      do 7 eexists. split_vc.
      eapply POST.
      unfold stk_env.
      split_vc. }
    build_vc idtac. }
  intros m s (? & ? & POST). subst.
  unfold stk_env.
  eexists a1. split_vc.
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


Lemma extend_array_spec : forall (Q : memory -> stack -> Prop),
  HT cblock table
   extend_array
   (fun m s => exists a vs x s0 t1 t2,
                 s = (Vptr (a, 0),t1):::(x,t2):::s0 /\
                 memarr m a vs /\
                 Mem.stamp a = Kernel /\
                 (forall r m1 t,
                    extends m m1 ->
                    Mem.get_frame m r = None ->
                    Mem.stamp r = Kernel ->
                    memarr m1 r (vs++[x]) ->
                    Q m1 ((Vptr (r, 0),t):::s0)))
   Q.

Proof.
  intros. unfold extend_array.

  build_vc ltac:(try apply copy_spec; try apply alloc_array_spec). auto.

  intros m ? (a & vs & x & s & t1 & t2 & ? & ARR & STAMPa & POST). subst.
  destruct ARR. subst.
  simpl.
  eexists. split; eauto.
  do 4 eexists.
  do 3 (split; eauto).
  do 6 eexists.
  do 2 (split; try reflexivity).
  do 3 eexists.
  do 2 (split; try reflexivity; try omega).
  intros b m' t' EXT VALID [t'' LOAD'] FRESH STAMPb.
  assert (NEQab : a <> b).
  { intros contra. subst. unfold load in LOAD. simpl in *.
    destruct (Mem.get_frame m b); congruence. }
  eexists. split; try reflexivity.
  assert (LOAD'' := extends_load _ _ _ _ EXT LOAD).
  do 4 eexists.
  do 3 (split; eauto).
  do 9 eexists.
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
  intros m'' t1' t2' t3' (COPY & EQLOAD & EQFRAME).
  simpl in COPY.
  assert (EQFRAME' : forall b' off, b' <> b -> load (b', off) m'' = load (b', off) m').
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
  do 6 eexists. do 2 (split; try reflexivity).
  do 6 eexists. do 2 (split; try reflexivity).
  do 4 eexists. do 3 (split; eauto).
  do 4 eexists. do 3 (split; eauto).
  do 4 eexists. do 3 (split; eauto).
  assert (STORE : valid_address (b,1 + Z.of_nat (length vs) + 0) m'').
  { unfold valid_address.
    rewrite EQLOAD; try omega.
    apply VALID. omega. }
  eapply valid_store in STORE. destruct STORE as [m''' STORE].
  do 5 eexists. split; [|split; eauto]; eauto.
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
            unfold load. simpl in *.
            destruct (Mem.get_frame m a) as [fr|] eqn:FRAME; try congruence.
            apply EXT in FRAME.
            rewrite FRAME.
            reflexivity.
          - intros contra.
            assert (1 + z = 1 + Z.of_nat (length vs) + 0) by congruence.
            omega. }
      * econstructor; try solve [constructor].
        replace (1 + Z.of_nat (length vs) + 0) with (1 + Z.of_nat (length vs)) in STORE by ring.
        erewrite load_store_new; eauto.
Qed.

End with_hints.

End with_cblock.
