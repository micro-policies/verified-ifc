(** Code, specifications, proofs for manipulating arrays in kernel memory *)

Require Import ZArith.
Require Import List.
Require Import Utils.
Require Import LibTactics.
Import ListNotations. 

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
Section with_systable.
Context {T: Type}.
Variable  SysTable : syscall_table T.

Notation HT := (HT SysTable).
Notation HTEscape := (HTEscape SysTable).

Ltac apply_wp :=
  try unfold pop, nop, push, dup, swap;
  match goal with
  | |- HT [Store] _ _ => eapply store_spec_wp'
  | |- HT [Add] _ _  => eapply add_spec_wp'
  | |- HT [Dup ?N] _ _ => eapply dup_spec_wp
  | |- HT [Swap ?N] _ _ => eapply swap_spec_wp
  | |- HT [Load] _ _ => eapply load_spec_wp'
  | |- HT [Push ?N] _ _ => eapply push_spec_wp
  | |- HT [Pop] _ _ => eapply pop_spec_wp
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

(* TODO: Move to CodeSpecs.v *)
Lemma extends_update : forall m m1 m2 a x v, 
  extends m m1 ->
  upd_m a (x,v) m1 = Some m2 ->
  ~ valid_address a m ->
  extends m m2.                        
Proof.
  unfold extends.  intros. pose proof (H _ _ H2). erewrite <- update_list_Z_spec2; eauto.
    intro. subst. eapply H1. eapply index_list_Z_valid; eauto.
Qed.

Hint Resolve extends_update. 

(* Memory copy.  *)

(* Initial stack:  count :: dst0 :: src0 :: _
   Final stack:    0 :: dst0 :: src0 :: _
   Side Effects: copies (src0,src0+count] to (dst0,dst0+count]  (provided these regions are disjoint) *)

Definition copy :=
  genRepeat ([Dup 2] ++ [Dup 1] ++  [Add] ++ [Load] ++ [Dup 2] ++ [Dup 2] ++  [Add] ++ [Store]).

(* The loop invariant for copy. *)
Definition Icopy (sz:Z) (dst:Z) (src:Z) m0 s0 :=
  fun m s => 
    exists cnt, s = (cnt,handlerTag):::(dst,handlerTag):::(src,handlerTag):::s0 /\
    (cnt <= sz) /\
    (forall z, src < z <= src+cnt -> valid_address z m) /\
    (forall z, dst < z <= dst+cnt -> valid_address z m) /\
    (forall z1 z2, src < z1 <= src+sz -> dst < z2 <= dst+sz -> z1 <> z2) (* disjoint *) /\
    (forall z, cnt < z <= sz -> read_m (src+z) m = read_m (dst+z) m) /\
    (forall z, ~ (dst+cnt < z <= dst+sz) -> read_m z m = read_m z m0).

(* These are no longer strictly necessary, but they might be easier to understand
than the combined proof...
Lemma copy_spec : forall sz dst src s0 m0,
  0 <= sz -> 
  HT copy 
  (fun m s => Icopy sz dst src m0 s0 m s /\ hd (CData(0,handlerTag)) s = CData(sz,handlerTag))
  (fun m s => Icopy sz dst src m0 s0 m s /\ hd (CData(0,handlerTag)) s = CData(0,handlerTag)).
Proof.
  intros. unfold copy. 
  apply HT_consequence with
   (P := (fun m s => exists s', s = CData(sz,handlerTag)::s' /\ Icopy sz dst src m0 s0 m s)) 
   (Q := (fun m s => exists s', s = CData(0,handlerTag)::s' /\ Icopy sz dst src m0 s0 m s)).
  eapply genRepeat_spec; eauto. 
  intros. 

  unfold Icopy.
  build_vc ltac:idtac.
  split_vc. 
  rewrite H1 in H2. inv H2. 
  destruct (valid_read (x0 + src) m) as [(v,vl) E].
    intuition. 
  destruct (valid_store (x0 + dst) (v,vl) m) as [m' W].
    intuition.
  split_vc. 
  split. intros. eapply valid_address_upd; eauto; intuition.  
  split. intros. eapply valid_address_upd; eauto; intuition.
  split_vc. 
  split. intros. destruct (Z.eq_dec x0 z). 
    subst.  
      assert (read_m (z + dst) m' = Some (v,vl)). 
          erewrite update_list_Z_spec; eauto. 
      assert (read_m (z+src) m' = Some (v,vl)).
          erewrite <- update_list_Z_spec2.
          eapply E. eapply W. eapply H6; omega. 
      replace (src + z) with (z+src) by omega. replace (dst + z) with (z+dst) by omega. congruence.
    assert (x0 < z <= sz).  omega. clear n H1. 
      assert (read_m (src+z) m' = read_m (src+z) m). 
         erewrite <- update_list_Z_spec2. eauto.
         eauto. specialize (H6 (src+z) (dst+x0)). omega. 
      assert (read_m (dst + z) m' = read_m (dst+z) m). 
         erewrite <- update_list_Z_spec2. eauto.
         eauto. omega.
      rewrite H1. rewrite H9.  eauto. 
  intros. 
     erewrite <- update_list_Z_spec2. eapply H8;  intuition. eauto; intuition. intuition. 
      
  intros. inv H0. destruct s. inv H1. inv H0. inv H1. 
  simpl in H2. exists s. intuition congruence.

  intros. inv H0. inv H1. intuition.
Qed.


Lemma copy_spec' : forall sz dst src s0 m0,
  HT copy 
  (fun m s => 0 <= sz /\ Icopy sz dst src m0 s0 m s /\ hd (CData(0,handlerTag)) s = CData(sz,handlerTag))
  (fun m s => Icopy sz dst src m0 s0 m s /\ hd (CData(0,handlerTag)) s = CData(0,handlerTag)).
Proof.
 intros. 
 eapply HT_fold_constant_premise. intros. eapply copy_spec. auto. 
Qed.

Lemma copy_spec'' : forall sz dst src s0 m0,
  HT copy
  (fun m s => 0 <= sz /\
              s = (sz,handlerTag):::(dst,handlerTag):::(src,handlerTag):::s0 /\
              m = m0 /\
              (forall z, src < z <= src+sz -> valid_address z m) /\
              (forall z, dst < z <= dst+sz -> valid_address z m) /\
              (forall z1 z2, src < z1 <= src+sz -> dst < z2 <= dst+sz -> z1 <> z2))
  (fun m s => (forall z, 0 < z <= sz -> read_m (src+z) m = read_m (dst+z) m) /\
              (forall z, ~ (dst < z <= dst+sz) -> read_m z m = read_m z m0) /\
              s = (0,handlerTag):::(dst,handlerTag):::(src,handlerTag):::s0).
Proof.
  intros. 
  eapply HT_consequence.
  eapply copy_spec'. 
  intros m s [P1 [P2 [P3 [P4 [P5 P6]]]]].
  subst m0. 
  split. eauto.
  split. unfold Icopy. eexists. 
  repeat (split; eauto; try omega). 
  intros. exfalso; omega. 
  subst s. auto. 

  intros m s [P1 P0]. 
  unfold Icopy in P1. destruct P1 as [cnt [P1 [P2 [P3 [P4 [P5 [P6 P7]]]]]]].
  subst s. inv P0. 
  split. intros. 
  eauto. 
  split. intros. eapply P7. omega. 
  auto.
Qed.

Lemma copy_spec_wp : forall (Q : memory -> stack -> Prop),
  HT copy
  (fun m s => exists sz dst src s0,
                0 <= sz /\
                s = (sz,handlerTag):::(dst,handlerTag):::(src,handlerTag):::s0 /\
                (forall z, src < z <= src+sz -> valid_address z m) /\
                (forall z, dst < z <= dst+sz -> valid_address z m) /\
                (forall z1 z2, src < z1 <= src+sz -> dst < z2 <= dst+sz -> z1 <> z2) (* disjoint *) /\
                (forall m1, 
                   (forall z, 0 < z <= sz -> read_m (src+z) m1 = read_m (dst+z) m1) ->
                   (forall z, ~ (dst < z <= dst+sz) -> read_m z m1 = read_m z m) ->
                   Q m1 ((0,handlerTag):::(dst,handlerTag):::(src,handlerTag):::s0)))
  Q.
Proof.                
  intros. 
  eapply HT_strengthen_premise with 
  (fun m s => exists sz dst src s0 m0,
                0 <= sz /\
                m = m0 /\
                s = (sz,handlerTag):::(dst,handlerTag):::(src,handlerTag):::s0 /\
                (forall z, src < z <= src+sz -> valid_address z m) /\
                (forall z, dst < z <= dst+sz -> valid_address z m) /\
                (forall z1 z2, src < z1 <= src+sz -> dst < z2 <= dst+sz -> z1 <> z2) (* disjoint *) /\
                (forall m1, 
                   (forall z, 0 < z <= sz -> read_m (src+z) m1 = read_m (dst+z) m1) ->
                   (forall z, ~ (dst < z <= dst+sz) -> read_m z m1 = read_m z m) ->
                   Q m1 ((0,handlerTag):::(dst,handlerTag):::(src,handlerTag):::s0))).
  2: split_vc. 
  eapply HT_forall_exists. intro sz. 
  eapply HT_forall_exists. intro dst. 
  eapply HT_forall_exists. intro src. 
  eapply HT_forall_exists. intro s0.
  eapply HT_forall_exists. intro m0.
  eapply HT_consequence'.
  eapply copy_spec''. 
  split_vc. 
  split_vc. 
  subst s. eapply H5; eauto.  
Qed.
*)

Lemma copy_spec_wp : forall (Q : memory -> stack -> Prop),
  HT copy
  (fun m s => exists sz dst src s0,
                0 <= sz /\
                s = (sz,handlerTag):::(dst,handlerTag):::(src,handlerTag):::s0 /\
                (forall z, src < z <= src+sz -> valid_address z m) /\
                (forall z, dst < z <= dst+sz -> valid_address z m) /\
                (forall z1 z2, src < z1 <= src+sz -> dst < z2 <= dst+sz -> z1 <> z2) (* disjoint *) /\
                (forall m1, 
                   (forall z, 0 < z <= sz -> read_m (src+z) m1 = read_m (dst+z) m1) ->
                   (forall z, ~ (dst < z <= dst+sz) -> read_m z m1 = read_m z m) ->
                   Q m1 ((0,handlerTag):::(dst,handlerTag):::(src,handlerTag):::s0)))
  Q.
Proof.                
  intros. unfold copy. 
  eapply HT_strengthen_premise with 
  (fun m s => exists sz dst src s0 m0,
                0 <= sz /\
                m = m0 /\
                s = (sz,handlerTag):::(dst,handlerTag):::(src,handlerTag):::s0 /\
                (forall z, src < z <= src+sz -> valid_address z m) /\
                (forall z, dst < z <= dst+sz -> valid_address z m) /\
                (forall z1 z2, src < z1 <= src+sz -> dst < z2 <= dst+sz -> z1 <> z2) (* disjoint *) /\
                (forall m1, 
                   (forall z, 0 < z <= sz -> read_m (src+z) m1 = read_m (dst+z) m1) ->
                   (forall z, ~ (dst < z <= dst+sz) -> read_m z m1 = read_m z m) ->
                   Q m1 ((0,handlerTag):::(dst,handlerTag):::(src,handlerTag):::s0))).
  2: split_vc. 
  eapply HT_forall_exists. intro sz. 
  eapply HT_forall_exists. intro dst. 
  eapply HT_forall_exists. intro src. 
  eapply HT_forall_exists. intro s0.
  eapply HT_forall_exists. intro m0.
  eapply HT_fold_constant_premise; intro.
  rename Q into Q0. 
  eapply HT_consequence' with
    (P := (fun m s => exists s', s = CData(sz,handlerTag)::s' /\ Icopy sz dst src m0 s0 m s))  
    (Q := (fun m s => exists s', s = CData(0,handlerTag)::s' /\ Icopy sz dst src m0 s0 m s)). 
  eapply genRepeat_spec; eauto. 
  intros. 

  unfold Icopy.
  build_vc ltac:idtac.
  split_vc. 
  inv H1. 
  destruct (valid_read (x0 + src) m) as [(v,vl) E].
    intuition. 
  destruct (valid_store (x0 + dst) (v,vl) m) as [m' W].
    intuition.
  split_vc. 
  split. intros. eapply valid_address_upd; eauto; intuition.  
  split. intros. eapply valid_address_upd; eauto; intuition.
  split_vc. 
  split. intros. destruct (Z.eq_dec x0 z). 
    subst.  
      assert (read_m (z + dst) m' = Some (v,vl)). 
          erewrite update_list_Z_spec; eauto. 
      assert (read_m (z+src) m' = Some (v,vl)).
          erewrite <- update_list_Z_spec2.
          eapply E. eapply W. eapply H5; omega. 
      replace (src + z) with (z+src) by omega. replace (dst + z) with (z+dst) by omega. congruence.
    assert (x0 < z <= sz).  omega. clear n H1. 
      assert (read_m (src+z) m' = read_m (src+z) m). 
         erewrite <- update_list_Z_spec2. eauto.
         eauto. specialize (H5 (src+z) (dst+x0)). omega. 
      assert (read_m (dst + z) m' = read_m (dst+z) m). 
         erewrite <- update_list_Z_spec2. eauto.
         eauto. omega.
      rewrite H1. rewrite H9.  eauto. 
  intros. 
     erewrite <- update_list_Z_spec2. eapply H7;  intuition. eauto; intuition. intuition. 
      
  intros m s [E [S H1]]. subst.  eexists. split. eauto. unfold Icopy. 
  eexists; split; eauto. intuition. 

  intros. inversion H1 as [s' [R1 R2]]. clear H1. 
  destruct H0 as [m' [s'' [R3 [R4 [R5 [R6 [R7 R8]]]]]]].
  unfold Icopy in R2.  destruct R2 as [cnt [R9 [R10 [R11 [R12 [R13 [R14 R15]]]]]]].
  subst. inv R9. 
  eapply R8. eauto. intros. eapply R15. omega. 
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


Inductive memseq (m:memory) : Z -> list Z -> Prop :=
| memseq_nil : forall z, memseq m z nil
| memseq_cons : forall z v vs, read_m z m = Some(v,handlerTag) -> memseq m (z+1) vs -> memseq m z (v::vs)
.

Lemma memseq_valid : forall m a vs,
  memseq m a vs -> 
  forall z, a <= z < a + Z.of_nat(length vs) -> valid_address z m. 
Proof.
  induction 1; intros. 
  simpl in H. exfalso; omega. 
  simpl in H1.
  destruct (Z.eq_dec z z0). 
    subst. eapply index_list_Z_valid; eauto.
  eapply IHmemseq. zify; omega. 
Qed.

Hint Resolve memseq_valid.

Lemma memseq_read : forall m a vs,
  memseq m a vs -> 
  forall z, a <= z < a + Z.of_nat(length vs) -> exists v, read_m z m = Some(v,handlerTag).
Proof.
  induction 1; intros. 
  simpl in H. exfalso; omega. 
  simpl in H1. 
  destruct (Z.eq_dec z z0).
    subst. eexists; eauto.
  eapply IHmemseq. zify; omega. 
Qed.

Lemma memseq_app: forall m a vs1 vs2, 
  memseq m a (vs1 ++ vs2) <-> (memseq m a vs1 /\ memseq m (a + Z.of_nat(length vs1)) vs2).
Proof.
  intros. split.
  generalize dependent a.
  induction vs1; intros.
    simpl in *. 
    split. constructor.
    replace (a+0) with a by ring. auto.
    simpl in H. 
    inv H. 
    destruct (IHvs1 (a0+1) H4).
    split.
    econstructor; eauto.
    simpl (length (a::vs1)). replace (a0 + Z.of_nat (S (length vs1))) with (a0 + 1 + Z.of_nat(length vs1)) by (zify;omega). auto.
  generalize dependent a. 
  induction vs1; intros. 
    simpl in *. inv H. replace (a+0) with a in H1 by ring. auto.
    inv H. simpl. inv H0. econstructor; eauto.
    eapply IHvs1. split. auto. simpl (length (a::vs1)) in H1. 
    replace (a0 + 1 + Z.of_nat (length vs1)) with (a0 + Z.of_nat(S(length vs1))) by (zify;omega).  auto.
Qed.

Lemma memseq_eq : forall m1 m2 a1 a2 vs,
   (forall z,  0 <= z < Z.of_nat (length vs) -> read_m (a1+z) m1 = read_m (a2+z) m2) ->                     
   memseq m1 a1 vs -> memseq m2 a2 vs.                    
Proof.
intros.
generalize dependent a2. 
induction H0. 
 intros. constructor.
 intros.
 assert (read_m z m1 = read_m a2 m2). 
   replace z with (z+0) by ring. replace a2 with (a2+0) by ring. 
   eapply H1. simpl.  zify; omega. 
 destruct (read_m a2 m2) eqn:E. destruct a as (v0,l0). 
   rewrite H in H2.  simpl in H2.  inv H2. 
 econstructor. eauto. 
 eapply IHmemseq. intros.
 replace (z+1 + z0) with (z+(1+z0)) by omega. 
 replace (a2+1 + z0) with (a2+ (1+z0)) by omega. 
 eapply H1. simpl (length (v0::vs)). zify; omega. 
 rewrite H in H2. 
 inv H2.
Qed. 

Lemma memseq_drop :
  forall ms z p vs
         (MEM : memseq ms z vs),
    memseq ms (z + Z.of_nat p) (drop p vs).
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

Inductive memarr (m:memory) (a:Z) (vs:list Z) : Prop :=
| memarr_i : forall c, 
    read_m a m = Some(Z_of_nat c,handlerTag) -> 
    memseq m (a+1) vs -> 
    c = length vs -> 
    memarr m a vs. 

(* Array allocation.  *)

(* Initial stack: count :: _ 
   Final stack:  ptr-to-array :: _
   Side effects: allocates fresh array of size count *)

Definition alloc_array:= dup ++ push 1 ++ [Add] ++ alloc ++ dup ++ [Swap 2] ++ [Swap 1] ++ [Store]. 

(* a direct proof in wp form this time, just for variety. *)
Lemma alloc_array_spec_wp: forall (Q : memory -> stack -> Prop), 
  HT alloc_array 
     (fun m s => exists cnt s0, s = (cnt,handlerTag):::s0 /\
                                cnt >= 0 /\ 
                                (forall a m1, 
                                   extends m m1 -> 
                                   (forall p, a <= p <= a+cnt -> ~ valid_address p m) ->
                                   (forall p, a < p <= a+cnt -> valid_address p m1) -> 
                                   (read_m a m1 = Some(cnt,handlerTag)) -> 
                                   Q m1 ((a,handlerTag):::s0)))
     Q.                                  
Proof.
  intros. 
  Opaque Z.add. (* not sure why this is necessary this time *)
  unfold alloc_array.
  build_vc ltac: (try apply alloc_spec_wp). 
  split_vc'; intros.
  split_vc'; intros. 
  edestruct (valid_store a (x,handlerTag) m0) as [m1 U]. intuition. 
  split_vc. 
  eapply H0; eauto using valid_address_upd, update_list_Z_spec with zarith. 
Qed.


(* Sum array lengths *)

(* Initial stack:  array1 :: array2 :: _
   Final stack:    (l1+l2) :: array1 :: array2 :: _   
      where l1,l2 are lengths of array1,array2
   Side effects: none 
*)          

Definition sum_array_lengths := [Dup 1] ++ [Load] ++ [Dup 1] ++ [Load] ++ [Add]. 

Lemma sum_array_lengths_spec_wp : forall Q,
  HT sum_array_lengths
     (fun m s => exists a1 a2 s0 l1 l2,
                 s = (a2,handlerTag):::(a1,handlerTag):::s0 /\
                 read_m a2 m = Some(l2,handlerTag) /\
                 read_m a1 m = Some(l1,handlerTag) /\
                 Q m ((l2+l1,handlerTag):::(a2,handlerTag):::(a1,handlerTag):::s0))
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
  HT
   concat_arrays
   (fun m s => exists a2 a1 vs1 vs2 s0,
                   s = (a2,handlerTag):::(a1,handlerTag):::s0 /\ 
                   memarr m a1 vs1 /\ memarr m a2 vs2 /\
                   (forall r m1,
                      extends m m1 ->
                      (* This is a bit silly. If we want the minimum condition that will
                              make subsequent proofs go through, [~valid_address r m] will do.
                              If we want a more "natural" condition, then should use
                              [forall p, r <= p <= r+(length (vs1++vs2)) -> ~valid_address p m] *)
                      (exists cnt, 
                         cnt >= 0 /\
                         (forall p, r <= p <= r+cnt -> ~ valid_address p m)) ->
                      memarr m1 r (vs1++vs2) ->
                      Q m1 ((r,handlerTag):::s0)))
   Q.
Proof.                                 
  intros. unfold concat_arrays. 

  build_vc ltac:(try apply copy_spec_wp; try apply alloc_array_spec_wp; try apply sum_array_lengths_spec_wp).

  split_vc. 
  inv H; split_vc. 
  inv H0; split_vc. 
  split.  instantiate (1:= Z.of_nat (length x1)); omega. 
  split_vc. 
  split. intros. eapply extends_valid_address; eauto with zarith. 
  split. intros. eauto with zarith. 
  split. intros. intro; subst.  pose proof (memseq_valid _ _ _ H3). eapply H5. instantiate (1:= z2). omega. 
    eapply H10. omega. 
  split_vc. 
  split. erewrite H9. eapply H0. eauto. intro. eapply H5. instantiate (1:= x0). omega. 
    eapply index_list_Z_valid; eauto.  
  split_vc. 
  split. erewrite H9. eapply H0. eauto. intro. eapply H5.  instantiate (1:=x).  omega. 
    eapply index_list_Z_valid; eauto.
  split_vc. 
  split.  instantiate (1:= Z.of_nat (length x2)). omega. 
  split_vc. 
  split. intros. assert (valid_address z m). apply (memseq_valid _ _ _ H4).  omega. 
    destruct (valid_read _ _ H11) as [v ?]. apply H0 in H12. erewrite <- H9 in H12. eapply index_list_Z_valid; eauto.
    intro.  eapply (H5 z). omega. auto.
  split. intros. assert (valid_address z m1). eapply H6. omega. 
    destruct (valid_read _ _ H11) as [v ?]. erewrite <- H9 in H12. eapply index_list_Z_valid; eauto. omega. 
  split. intros. intro; subst. eapply H5.  instantiate (1:= z2).  omega. apply (memseq_valid _ _ _ H4); eauto. omega. 
  split_vc. 
  eapply H1. 
  unfold extends. intros. 
  assert (valid_address p m).  eapply index_list_Z_valid; eauto. 
  apply H0 in H12.  erewrite <- H9 in H12. erewrite <- H11 in H12. auto.
   intro. eapply H5; eauto; omega. 
   intro. eapply H5; eauto; omega. 
   { eexists; split; eauto. 
     omega. }
  econstructor. 
  replace (Z.of_nat (length x2) + Z.of_nat (length x1)) with (Z.of_nat (length x2 + length x1)) in H7 by (zify;omega).  
  erewrite H11. rewrite H9.  eapply H7.  omega.  omega. 
  2: rewrite app_length; omega. 
  assert (forall z: Z, 0 < z <= (Z.of_nat(length x1)) -> read_m (a+z) m2 = read_m (x0+z) m). 
    intros. destruct (read_m (x0+z) m) eqn:E.  
    destruct a0 as (v0,l0).  rewrite H11. rewrite <- H8. rewrite H9. apply H0 in E. auto.  
    intro. eapply H5.  instantiate (1:= x0+z).  omega. eapply index_list_Z_valid; eauto. 
    auto.
    intro. omega. 
    destruct (memseq_read _ _ _ H3 (x0+z)) as [v ?].  omega. 
    rewrite H13 in E; inv E. 
  assert (forall z:Z, 0 < z <= Z.of_nat(length x2) ->
                      read_m (a + Z.of_nat(length x1) + z) m2 = read_m (x + z) m).
    intros. destruct (read_m (x+z) m) eqn: E.
    destruct a0 as (v0,l0).  replace (a + Z.of_nat (length x1) + z) with (Z.of_nat (length x1) + a + z) by omega.
      rewrite <- H10. rewrite H11. rewrite H9. apply H0 in E. auto.  
    intro. eapply H5. instantiate (1:=x+z).  omega. eapply index_list_Z_valid; eauto.
    intro. eapply H5. instantiate (1:=x+z).  omega.  eapply index_list_Z_valid; eauto. 
    auto.
    destruct (memseq_read _ _ _ H4 (x+z)) as [v ?]. omega.
    rewrite H14 in E; inv E. 
  apply memseq_app. split.
  eapply memseq_eq. 2: eauto. intros. replace (a+1+z) with (a+(1+z)) by omega. 
    replace (x0+1+z) with (x0+(1+z)) by omega. rewrite H12. auto. omega. 
  eapply memseq_eq. 2: eauto. intros. 
    replace (a + 1 + Z.of_nat (length x1) + z) with (a+ Z.of_nat (length x1) + (1+z)) by omega. 
    replace (x+1+z) with (x+(1+z)) by omega. rewrite H13. auto. omega. 
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
Definition Ifab (f : memory -> stack -> Z -> Z -> Z)  (n: memory -> stack -> Z) (a:Z) (vs:list Z) m0 s0 := 
    fun m s =>
      exists i v,
        i <= Z.of_nat (length(vs)) /\
        memarr m a vs /\
        m = m0 /\
        s = (i,handlerTag):::(v,handlerTag):::(a,handlerTag):::s0  /\
        v = fold_right (f m0 s0) (n m0 s0) (dropZ i vs).


Lemma fab_spec : forall gen_f f n a vs m0 s0 i,
  (forall (Q: memory -> stack -> Prop),
  HT gen_f 
     (fun m s => exists x v ign0 ign1 ign2,
                   s = (x,handlerTag):::(v,handlerTag):::(ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0 
                 /\ m = m0 /\
                 Q m (((f m0 s0) x v,handlerTag):::(ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0))
      Q) ->
  HT (fold_array_body gen_f)
  (fun m s => exists s', s = (i,handlerTag):::s' /\ i > 0 /\ Ifab f n a vs m0 s0 m s)
  (fun m s => exists s', s = (i,handlerTag):::s' /\ Ifab f n a vs m0 s0 m ((Z.pred i,handlerTag):::s')).
Proof.

  intros.
  unfold fold_array_body.
  build_vc ltac:(try apply H). 
  split_vc. 
  destruct H1 as [i' [ v' [? [? [? [? ?]]]]]]. subst.  inv H4.  inv H2. 
  destruct (memseq_read _ _ _ H4 (i'+a)) as [v ?].  zify; omega. 
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
  apply (memseq_drop _ _ p) in H4.
  generalize (@drop_cons _ p vs).
  intros HH.
  assert (p < length vs)%nat.
  { zify. 
    rewrite Z2Nat.id in Heqp; omega. }
  destruct HH as [v' Hv']; auto.
  rewrite Hv' in H4.
  inv H4.
  rewrite Z2Nat.id in H9; auto.
  assert (EE : a + 1 + Z.pred i' = i' + a) by omega.
  rewrite EE in H9.
  rewrite H9 in H2. inv H2.
  assumption.
Qed.


Lemma fold_array_spec: forall gen_f gen_n m0 s0 a vs n f,
  (forall (Q: memory -> stack -> Prop),
  HT gen_n 
     (fun m s => exists ign0,
                   s = (ign0,handlerTag):::s0 /\ m = m0 /\ 
                   Q m (((n m0 s0),handlerTag):::(ign0,handlerTag):::s0))
     Q) -> 
  (forall (Q: memory -> stack -> Prop),
  HT gen_f 
     (fun m s => exists x v ign0 ign1 ign2, 
                   s = (x,handlerTag):::(v,handlerTag):::(ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0 
                 /\ m = m0 /\
                 Q m (((f m0 s0) x v,handlerTag):::(ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0))
     Q) -> 
  memarr m0 a vs -> 
  HT (fold_array gen_n gen_f)
     (fun m s => s = (a,handlerTag):::s0 /\ m = m0)
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
 intros. destruct H3 as [s' [? ?]]. exists s'. intuition. 
 intros. destruct H3 as [m' [s' [s'0 [? ?]]]].
 destruct H5 as [i' [ v' [? [? [? [? ?]]]]]]. 
 simpl in H4. destruct H4 as [s'' [? ?]]. 
 destruct H10 as [i0 [v0 [? [? [? [? ?]]]]]]. subst. inv H8. inv H13. 
 eexists.  split. auto.  unfold Ifab. 
 eexists (Zpred i').
 eexists.
 split; eauto.  
 simpl. intros. 
 destruct H2 as [s' [? ?]]. 
 destruct H3 as [i' [ v' [? [? [? [? ?]]]]]]. subst. inv H6.
 do 3 eexists. split; eauto. 
 do 4 eexists. split; eauto. 
 split; eauto.
 split; eauto. 
 do 3 eexists. split; eauto. 

 simpl. instantiate 
          (1:= (fun m s => exists i s',
                             0 <= i /\ s = (i, handlerTag) ::: s' /\ Ifab f n a vs m0 s0 m s)).
 auto.
 2: instantiate (1:= (fun m s => s = (a, handlerTag) ::: s0 /\ m = m0)); auto.

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
  HT gen_n 
     (fun m s => exists ign0,
                   s = (ign0,handlerTag):::s0 /\ m = m0 /\ 
                   Q m (((n m0 s0),handlerTag):::(ign0,handlerTag):::s0))
     Q) -> 
  (forall (Q: memory -> stack -> Prop),
  HT gen_f 
     (fun m s => exists x v ign0 ign1 ign2, 
                   s = (x,handlerTag):::(v,handlerTag):::(ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0 
                 /\ m = m0 /\
                 Q m (((f m0 s0) x v,handlerTag):::(ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::s0))
     Q) -> 
  HT (fold_array gen_n gen_f)
     (fun m s => exists a vs,
                   memarr m0 a vs /\ s = (a,handlerTag):::s0 /\ m = m0 /\ 
                   Q m ((fold_right (f m0 s0) (n m0 s0) vs,handlerTag):::s0))
     Q.
Proof.
  intros. 
  eapply HT_forall_exists. intro a. 
  eapply HT_forall_exists. intro vs. 
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

Lemma boolToZ_existsb : forall f xs , boolToZ (existsb f xs) = fold_right (fun x v : Z => orz (boolToZ (f x)) v) 0 xs.
Proof.
  induction xs;  simpl; auto.
  destruct (f a); unfold orz in *; simpl; auto.
Qed.

Lemma exists_array_spec_wp : forall gen_f (f: memory -> stack -> Z -> bool) s0 m0,
  (forall (Q: memory -> stack -> Prop),
  HT gen_f 
     (fun m s => exists x ign0 ign1 ign2 ign3, 
                   s = (x,handlerTag):::(ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::(ign3,handlerTag):::s0 
                 /\ m = m0 /\
                 Q m ((boolToZ((f m0 s0) x),handlerTag):::(ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::(ign3,handlerTag):::s0)) 
     Q) -> 
  forall (Q: memory -> stack -> Prop),
  HT (exists_array gen_f) 
     (fun m s => exists a vs,
                      memarr m a vs /\ 
                      s = (a,handlerTag):::s0 /\ 
                      m = m0 /\
                      Q m ((boolToZ (existsb (f m s0) vs),handlerTag):::s0))
     Q.
Proof.
  intros.
  unfold exists_array. 
  eapply HT_strengthen_premise.
  eapply fold_array_spec_wp with 
           (n:= fun _ _ => boolToZ false)
           (f:= fun m0 s0 x v => orz (boolToZ (f m0 s0 x)) v); eauto. 
  intro. eapply HT_strengthen_premise. eapply genFalse_spec_wp. 
  split_vc. 
  intro.
  eapply HT_compose_flip.
  eapply genOr_spec_general_wp. 
  eapply HT_strengthen_premise.
  eapply H. 
  split_vc.  
  split_vc. rewrite boolToZ_existsb in H2.  auto.
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

Lemma boolToZ_forallb : forall f xs , boolToZ (forallb f xs) = fold_right (fun x v : Z => andz (boolToZ (f x)) v) 1 xs.
Proof.
  induction xs;  simpl; auto.
  destruct (f a); unfold andz in *; simpl; auto.
Qed.

Lemma forall_array_spec_wp : forall gen_f (f: memory -> stack -> Z -> bool) s0 m0,
  (forall (Q: memory -> stack -> Prop),
  HT gen_f 
     (fun m s => exists x ign0 ign1 ign2 ign3, 
                   s = (x,handlerTag):::(ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::(ign3,handlerTag):::s0 
                 /\ m = m0 /\
                 Q m ((boolToZ((f m0 s0) x),handlerTag):::(ign0,handlerTag):::(ign1,handlerTag):::(ign2,handlerTag):::(ign3,handlerTag):::s0)) 
     Q) -> 
  forall (Q: memory -> stack -> Prop),
  HT (forall_array gen_f) 
     (fun m s => exists a vs,
                      memarr m a vs /\ 
                      s = (a,handlerTag):::s0 /\ m = m0 /\
                      Q m ((boolToZ (forallb (f m s0) vs),handlerTag):::s0))
     Q.
Proof.
  intros.
  unfold forall_array. 
  eapply HT_strengthen_premise.
  eapply fold_array_spec_wp with 
           (n:= fun _ _ => boolToZ true)
           (f:= fun m0 s0 x v => andz (boolToZ (f m0 s0 x)) v); eauto. 
  intro. eapply HT_strengthen_premise. eapply genTrue_spec_wp. 
  split_vc. 
  intro.
  eapply HT_compose_flip.
  eapply genAnd_spec_general_wp. 
  eapply HT_strengthen_premise.
  eapply H. 
  split_vc. 
  split_vc. rewrite boolToZ_forallb in H2.  auto.
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

Definition Z_list_in_b (x: Z) (xs:list Z) : bool :=
  existsb (fun x' => x =? x') xs.

Lemma in_array_spec: forall a vs x s0 m0,
  memarr m0 a vs -> 
  HT
    in_array
    (fun m s => s = (a,handlerTag):::(x,handlerTag):::s0 /\ m = m0)
    (fun m s => s = (boolToZ(Z_list_in_b x vs),handlerTag):::s0 /\ m = m0)
.
Proof.
  intros. unfold in_array.
  eapply HT_strengthen_premise.
  eapply HT_compose_flip. 
  build_vc idtac.
  eapply exists_array_spec_wp with (f := fun _ _ y => x =? y) (s0 := (x,handlerTag):::s0). 
  intros. 
  eapply HT_compose_flip. 
  eapply genEq_spec_wp. 
  eapply HT_strengthen_premise.
  eapply dup_spec_wp.
  split_vc. 
  split_vc. 
Qed.

Lemma in_array_spec_wp : forall (Q: memory -> stack -> Prop), 
  HT 
    in_array
    (fun m s => exists a vs x s0 m0,
                  memarr m0 a vs /\
                  s = (a,handlerTag):::(x,handlerTag):::s0 /\ 
                  m = m0 /\
                  Q m0 ((boolToZ(Z_list_in_b x vs),handlerTag):::s0))
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
  simpl. intros. destruct H0 as [m' [s' [? [? ?]]]]. destruct H1. subst. auto. 
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


Definition Z_list_subset_b (xs1 xs2:list Z) : bool :=
  forallb (fun x1 => Z_list_in_b x1 xs2) xs1. 

Lemma subset_arrays_spec : forall a1 a2 vs1 vs2 s0 m0,
  memarr m0 a1 vs1 ->
  memarr m0 a2 vs2 -> 
  HT subset_arrays
     (fun m s => s = (a1,handlerTag):::(a2,handlerTag):::s0 /\ m = m0)
     (fun m s => s = ((boolToZ (Z_list_subset_b vs1 vs2),handlerTag):::s0) /\ m = m0).
Proof.
  intros. unfold subset_arrays.
  eapply HT_compose_flip. 
  build_vc idtac.
  eapply HT_strengthen_premise.
  eapply forall_array_spec_wp with (f := fun _ s0 y => Z_list_in_b y vs2) (s0 := (a2,handlerTag):::s0). 
  intros. 
  eapply HT_compose_flip. 
  eapply in_array_spec_wp. 
  eapply HT_strengthen_premise.
  eapply dup_spec_wp.
  split_vc. clear H0. 
  split_vc. 
Qed.

Lemma subset_arrays_spec_wp : forall (Q: memory -> stack -> Prop), 
  HT 
    subset_arrays
    (fun m s => exists a1 a2 vs1 vs2 s0 m0,
                  memarr m0 a1 vs1 /\
                  memarr m0 a2 vs2 /\
                  s = (a1,handlerTag):::(a2,handlerTag):::s0 /\ 
                  m = m0 /\
                  Q m0 ((boolToZ(Z_list_subset_b vs1 vs2),handlerTag):::s0))
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
  eapply HT_consequence'. eapply subset_arrays_spec with (a1:=a1) (a2:=a2); eauto. 
  simpl. intros. intuition jauto. 
  simpl. intros. destruct H1 as [m' [s' [? [? ?]]]]. destruct H2. subst. auto. 
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
  HT
   extend_array
   (fun m s => exists a vs x s0,
                 s = (a,handlerTag):::(x,handlerTag):::s0 /\
                 memarr m a vs /\
                 (forall r m1,
                    extends m m1 ->
                    ~ valid_address r m ->
                    memarr m1 r (vs++[x]) ->
                    Q m1 ((r,handlerTag):::s0)))
   Q.
                     
Proof.                                 
  intros. unfold extend_array. 

  build_vc ltac:(try apply copy_spec_wp; try apply alloc_array_spec_wp). 

  split_vc. 
  inv H. 
  Opaque Z.add. (* not sure why this is necessary this time *)
  split_vc. 
  split.  instantiate (1:= Z.of_nat (length x0)); omega. 
  split_vc. 
  split. intros. eapply extends_valid_address; eauto. eapply memseq_valid; eauto. omega. 
  split. intros. eapply H4. omega. 
  split. intros.  intro. subst. eapply H3. instantiate (1:= z2).  omega.  eauto with zarith. 
  split_vc. 
  (* rather luckily, we stop here, which is the earliest point where we can assert the following *)
  destruct (valid_store (1+Z.of_nat (length x0) + a) (x1,handlerTag) m0) as [m' W].
    edestruct (valid_read (1+ Z.of_nat (length x0) + a)).  eapply H4.  omega.  
    eapply index_list_Z_valid; eauto.  rewrite H7; try omega.  eauto.
  split. rewrite H7.  erewrite <- H. eauto. eauto.  intro.  eapply H3. instantiate (1:= x).  omega.  
     eapply index_list_Z_valid; eauto. 
  split_vc. 
  eapply H0. 
  unfold extends. intros.
  erewrite <- update_list_Z_spec2.  2: eauto. erewrite H7. eapply H. eauto. 
    intro. eapply H3.  instantiate (1:= p). omega.  eapply index_list_Z_valid; eauto. 
    intro. subst. eapply H3. instantiate (1:= (1 + Z.of_nat (length x0) + a)). omega. eapply index_list_Z_valid; eauto.
  eapply H3; omega. 
  econstructor.  
    3: rewrite app_length; simpl; eauto. 
    replace (Z.of_nat (S(length x0+0))) with (1 +Z.of_nat(length x0)) by (zify;omega).     
    erewrite <- update_list_Z_spec2. 2:eauto. rewrite H7. eauto.
    intro. omega. 
    intro. omega. 
  assert (forall z, 0 < z <= (Z.of_nat(length x0)) -> read_m (a+z) m' = read_m (x+z) m). 
    intros.  erewrite <- update_list_Z_spec2. 2:eauto. 
        rewrite <- H6.  rewrite H7.  
        destruct (memseq_read _ _ _ H2 (x+z)).  omega. pose proof (H _ _ H9). rewrite H9. auto.
        intro. eapply H3. instantiate (1:= x+z).  omega.  eapply memseq_valid. eauto. omega. omega. 
        intro. omega. 
  apply memseq_app; split.
  eapply memseq_eq; intros. 2:eauto. replace (x+1+z) with (x+(1+z)) by omega. 
     replace (a+1+z) with (a+(1+z)) by omega. erewrite <- H8.  eauto. omega. 
  econstructor. 2: constructor.  
     apply update_list_Z_spec in W. unfold Atom in W. (* argh *) rewrite <- W.  f_equal. omega. 
Qed.

End with_hints.

End with_systable.
