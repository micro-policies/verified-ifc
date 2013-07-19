(* Specifications for (privileged) machine code instructions and generators. *)

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
Require Import ConcreteExecutions.
Require Import ConcreteMachine.
Require Import Coq.Arith.Compare_dec.

Definition extends (m1 m2: list (@Atom Z)) : Prop :=
 forall p v, read_m p m1 = Some v -> read_m p m2 = Some v.

Lemma extends_refl : forall m, extends m m.
Proof.
  unfold extends; intros; auto.
Qed.

Lemma extends_trans: forall m1 m2 m3, extends m1 m2 -> extends m2 m3 -> extends m1 m3. 
Proof.
  unfold extends; intros; auto.
Qed.

Definition extension_comp (P: list (@Atom Z) -> list CStkElmt -> Prop) := 
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

Context {T:Type}.
Variable SysTable : syscall_table T.
Notation cstep := (cstep SysTable).
Notation runsToEnd := (runsToEnd SysTable).
Notation runsToEscape := (runsToEscape SysTable).
Notation HT := (HT SysTable).
Notation HTEscape := (HTEscape SysTable).

(* To stop struggling with [replace]s *)
Lemma cstep_branchnz_p' : forall c m fh i s pcv pcl offv av al pc',
       read_m pcv fh = Some (BranchNZ offv) ->
       pc' = (if av =? 0 then pcv + 1 else pcv + offv) ->
       cstep (CState c m fh i ((av, al) ::: s) (pcv, pcl) true) Silent
             (CState c m fh i s (pc',handlerTag) true).
Proof.
  intros. subst.
  constructor; auto.
Qed.

(* ========= Facts about memory ====================== *)

(* NC: to prove that addresses are valid per this definition, we just
   need to know that that the memory is at least as large as the
   [tmuCacheSize] defined in Concrete.v, since we only use
   [valid_address] assumptions for [addrTag*]. *)
Definition valid_address a (m: memory) :=
  (0 <= a) /\ (Z.to_nat a < length m)%nat.

Lemma valid_read: forall a m,
  valid_address a m ->
  exists v, read_m a m = Some v.
Proof.
  introv H.
  unfold valid_address in H.
  unfold read_m.
  cases (a <? 0).
  - false.
    rewrite Z.ltb_lt in Eq. omega.
  - remember (Z.to_nat a) as n; clear Heqn.
    destruct H as [_ Hbound].
    generalize dependent n.
    generalize dependent m.
    induction m; intros.
    + false; simpl in *; omega.
    + cases n; subst.
      * simpl; eauto.
      * simpl in Hbound.
        apply lt_S_n in Hbound.
        eauto.
Qed.

Lemma valid_store: forall a v m,
  valid_address a m ->
  exists m', upd_m a v m = Some m'.
Proof.
  intros.
  unfold valid_address in H. 
  eapply update_list_Z_Some; iauto.
Qed. 

Lemma valid_address_upd: forall a a' vl m m',
  valid_address a m ->
  upd_m a' vl m = Some m' ->
  valid_address a m'.
Proof.
  unfold valid_address; intuition.
  unfold upd_m in *.
  destruct (a' <? 0).
  - false.
  - erewrite update_preserves_length; eauto.
Qed.


Lemma extends_valid_address: forall m m' a, 
                               valid_address a m ->
                               extends m m' ->
                               valid_address a m'.
Proof.
  intros.
  exploit valid_read; eauto. intros [v Hread].
  unfold valid_address, extends in * ; intros.
  intuition.
  exploit H0; eauto. intros.
  eapply index_list_Z_valid; eauto.
Qed.

(* ================================================================ *)
(* Specs for individual instructions *)

(* There is indeed a [Noop] instruction (why??), but these specs are 
   actually describing the empty instruction sequence. *)
   
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
  exists cache0.
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

Lemma nop_spec_wp: forall Q,
  HT [Noop] Q Q.
Proof.
  unfold CodeTriples.HT; simpl; intros.
  eexists; eexists; intuition eauto. subst.

  (* Run an instruction *)
  eapply rte_step; eauto.
  eapply cstep_nop_p ; eauto.
Qed.

Lemma add_spec: forall (z1 z2: Z) (l1 l2: Z) (m: memory) (s: stack),
  HT  [Add]
      (fun m1 s1 => m1 = m /\ s1 = CData (z1,l1) :: CData (z2,l2) :: s)
      (fun m2 s2 => m2 = m /\ s2 = CData (z1 + z2, handlerTag) :: s).
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
  eapply rte_step; auto.
  eapply cstep_add_p ; eauto.
Qed.

Lemma add_spec_I: forall (z1 z2: Z) (l1 l2: Z) (I: memory -> stack -> Prop),
  HT  [Add]
      (fun m1 s1 => 
         match s1 with 
             | CData (z,l) :: CData (z',l') :: s => 
               z = z1 /\ z' = z2 /\ l = l1 /\ l' = l2 /\ I m1 s
             | _ => False
         end)
      (fun m2 s2 => 
         match s2 with 
             | CData (z,l) :: s =>  z = z1+z2 /\ l = handlerTag /\ I m2 s
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
  substs.
  eexists.
  eexists.

  (* Run an instruction *)
  intuition.

  Focus 2. 
  eapply rte_step; eauto.
  eapply cstep_add_p ; eauto.
  (* Finish running *)
  simpl. auto.
Qed.

(* not actually helpful in this form *)
Lemma add_spec_wp: forall Q z1 z2 m s,
  HT [Add]
     (fun m0 s0 => s0 = (z1,handlerTag) ::: (z2,handlerTag) ::: s /\
                   m0 = m /\
                   Q m ((z1+z2,handlerTag) ::: s))
     Q.
Proof.
  intros. 
  unfold CodeTriples.HT. intros. intuition. subst.
  eexists. eexists.  split.  eauto.

  (* Load an instruction *)
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_add_p; eauto.
Qed.

(* better *)
Lemma add_spec_wp': forall Q,
  HT [Add]
     (fun m0 s0 => 
        exists z1 z2 s,   
          s0 = (z1,handlerTag) ::: (z2,handlerTag) ::: s /\
          Q m0 ((z1+z2,handlerTag) ::: s))
     Q.
Proof.
  intros. 
  unfold CodeTriples.HT. intros imem mem stk0 cache0 fh n n' H [z1 [x2 [s [E1 E2]]]]. intros. simpl in H0. subst.
  eexists. eexists. split. eauto.

  (* Load an instruction *)
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_add_p; eauto.
Qed.



Lemma sub_spec: forall z1 l1 z2 l2, forall m0 s0,
  HT [Sub]
     (fun m s => m = m0 /\ s = (z1,l1) ::: (z2,l2) ::: s0)
     (fun m s => m = m0 /\ s = (z1 - z2,handlerTag) ::: s0).
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
  eapply rte_step; auto.
  eapply cstep_sub_p; eauto.
Qed.


Lemma sub_spec_I: forall (z1 z2: Z) (l1 l2: Z) (I: memory -> stack -> Prop),
  HT  [Sub]
      (fun m1 s1 => 
         match s1 with 
             | CData (z,l) :: CData (z',l') :: s => 
               z = z1 /\ z' = z2 /\ l = l1 /\ l' = l2 /\ I m1 s
             | _ => False
         end)
      (fun m2 s2 => 
         match s2 with 
             | CData (z,l) :: s =>  z = z1-z2 /\ l = handlerTag /\ I m2 s
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
  substs.
  eexists.
  eexists.

  (* Run an instruction *)
  intuition.

  Focus 2. 
  eapply rte_step; eauto.
  eapply cstep_sub_p ; eauto.
  
  (* Finish running *)
  simpl. auto.
Qed.



Lemma dup_spec_wp: forall P n,
  HT   (Dup n :: nil)
       (fun m s => exists x, index_list n s = Some x /\ P m (x :: s))
       P.
Proof.
  intros P n.
  unfold CodeTriples.HT. 
  intros imem mem0 stk0 c0 fh0 n0 n0' Hcode [x [HI HP]] Hn'.
  eexists. eexists. intuition. eauto.
  
  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. simpl in *. intuition. 

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_dup_p ; eauto.
Qed.

(* not used *)
Lemma dup_spec'': forall n m0 s0 x,
  HT (Dup n::nil)
     (fun m s => m = m0 /\ s = s0 /\ index_list n s0 = Some x)
     (fun m s => m = m0 /\ s = x::s0). 
Proof.
  intros.
  intros imem mem0 stk0 c0 fh0 n0 n0' Hcode HP' Hn'.
  eexists.
  eexists.
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_dup_p; eauto.
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
  intros imem mem0 stk0 c0 fh0 n0 n0' Hcode [y [s0 [x [s' [HE [HI [HU HP]]]]]]] Hn'.
  eexists. eexists. intuition. eauto.
  
  (* Load an instruction *)
  subst. simpl.
  unfold code_at in *. simpl in *. intuition. 

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_swap_p ; eauto.
Qed.

Example swap_ex: forall a b s0 m0,
  HT [Swap 1]
     (fun m s => s = a:::b:::s0 /\ m = m0)
     (fun m s => s = b:::a:::s0 /\ m = m0).
Proof.
  intros.
  eapply HT_strengthen_premise.
  eapply swap_spec_wp. 
  intros. inv H. 
  eexists. eexists.  eexists. eexists.
  split; eauto.  split. simpl; eauto. split. simpl; eauto. split. auto. auto. 
Qed.



Lemma push_spec: forall v P,
  HT   (Push v :: nil)
       (fun m s => P m (CData (v,handlerTag) :: s))
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
  eapply rte_step; auto.
  eapply cstep_push_p ; eauto.
Qed.


Lemma push_spec': forall v P,
  HT   (Push v :: nil)
       P
       (fun m s => head s = Some (CData (v,handlerTag)) /\
                            P m (tail s)).
Proof.
  intros v P.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP Hn'.
  exists (CData (v, handlerTag) :: stk0). eexists c0.
  intuition.
  
  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold code_at in *. intuition. 

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_push_p ; eauto.
Qed.

(* Ghost variable style *)
(* NC: to write a generic instruction-verification tactic, it seems we
   may only need to factor out the specific unfoldings (here [push'])
   and the specific step lemmas (here [cp_push]). *)
Lemma push_spec'': forall v, forall m0 s0,
  HT (push v)
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = CData (v,handlerTag) :: s0).
Proof.
  intros.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP' Hn'.
  eexists.
  eexists.
  intuition.

  (* Load an instruction *)
  subst. simpl.
  unfold skipNZ in *.
  unfold push, code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_push_p; eauto.
Qed.

Lemma push_spec_I: forall v I,
  HT (push v)
     I
     (fun m s => match s with 
                   | CData (z,t)::tl => I m tl /\ v = z /\ t = handlerTag
                   | _ => False
                 end).
Proof.
  intros.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP' Hn'.
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
     (fun m s0 => Q m ((i,handlerTag):::s0))
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

Lemma pop_spec_I: forall v vl I, 
  HT [Pop]
     (fun m s => match s with 
                     | CData (z,l) :: tl => v = z /\ l = vl /\ I m tl
                     | _ => False
                 end)
     (fun m s => I m s).
Proof.
  unfold CodeTriples.HT.
  intros.
  subst. simpl.
  destruct stk0 as [| a tl]; try solve [intuition].
  destruct a as [z l|]; try solve [intuition].
  destruct z. intuition. subst.
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



Lemma load_spec: forall a al v vl, forall m0 s0,
  index_list_Z a m0 = Some (v,vl) ->
  HT [Load]
     (fun m s => m = m0 /\ s = CData (a,al) :: s0)
     (fun m s => m = m0 /\ s = CData (v,vl) :: s0).
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
  eapply rte_step; auto.
  eapply cstep_load_p; eauto.
Qed.

Lemma load_spec_I: forall a v vl I,
  HT [Load]
     (fun m s => 
        match s with 
            | CData (z,al) :: tl => 
              a = z /\
              index_list_Z a m = Some (v,vl) /\
              I m tl 
            | _ => False
        end)
     (fun m s => 
        match s with 
            | CData (z,t) :: tl =>
              v = z /\ t = vl /\ I m tl
            | _ => False
        end).
Proof.
  intros a v vl I. unfold CodeTriples.HT.
  intros imem mem stk0 cache0 fh n n' Hcode HP' Hn'.
  subst.
  destruct stk0 as [| hd tl]; try solve [intuition].
  destruct hd as [a' |]; try solve [intuition].
  destruct a' as [a' ]. inv HP'.
  eexists. eexists.
  simpl in *.
  intuition. 

  Focus 2.

  (* Run an instruction *)
  eapply rte_step; auto.
  eapply cstep_load_p; eauto.
  simpl. auto.
Qed.

Lemma load_spec_wp: forall a v vl Q,
  forall s,
  HT [Load]
     (fun m s0 => s0 = (a,handlerTag) ::: s /\
                   index_list_Z a m = Some(v,vl) /\
                   Q m ((v,vl) ::: s))
     Q.
Proof.
  intros a v vl Q s.
  intros imem mem0 stk0 c0 fh0 n n' Hcode HP' Hn'.
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
     (fun m s0 => exists a v vl s, 
                    s0 = (a,handlerTag) ::: s /\
                   index_list_Z a m = Some(v,vl) /\
                   Q m ((v,vl) ::: s))
     Q.
Proof.
  intros. eapply HT_forall_exists. 
  intros. eapply HT_forall_exists. 
  intros. eapply HT_forall_exists. 
  intros. eapply HT_forall_exists. 
  eapply load_spec_wp. 
Qed.



Lemma store_spec: forall a al v vl m s,
  HT [Store]
     (fun m0 s0 => m0 = m /\
                   s0 = (a,al) ::: (v,vl) ::: s /\
                   valid_address a m) (* NC: better to move this outside? *)
     (fun m1 s1 => s1 = s /\
                   upd_m a (v,vl) m = Some m1).
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
  eapply rte_step; auto.
  eapply cstep_store_p; eauto.
Qed.

Lemma store_spec_I: forall a al v vl Is (Im: memory -> Z -> Prop),
                    forall (IMperAddr: forall m a m' v, 
                                         Im m a ->
                                         upd_m a v m = Some m' ->
                                         (forall a', a' <> a -> Im m' a')),
  HT [Store]
     (fun m s => 
        match s with 
            | (z1,zl) ::: (vz,vzl) ::: tl =>
              a = z1 /\ al = zl /\
              v = vz /\ vl = vzl /\
              valid_address a m /\
              Is tl /\ (forall a, Im m a)
            | _ => False
        end) 
     (fun m s => Is s /\ 
                 (forall addr, addr <> a -> Im m addr) /\
                 (read_m a m = Some (v,vl))).
Proof.
  unfold CodeTriples.HT.
  intros.
  subst.
  destruct stk0 ; try solve [intuition].
  destruct c as [[z1 zl] |] ; try solve [intuition].
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
  eapply update_list_Z_spec; eauto. 
Qed.



Lemma store_spec_wp: forall Q a al v,
  forall m s,
  HT [Store]
     (fun m0 s0 => s0 = (a,al) ::: v ::: s /\
                   upd_m a v m0 = Some m /\
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
  eapply rte_step; auto.
  destruct v.
  eapply cstep_store_p; eauto.
Qed.

Lemma store_spec_wp' : forall Q,
       HT [Store]
         (fun (m0 : memory) (s0 : stack) =>
          exists a al v m s, 
          s0 = (a, al) ::: v ::: s /\ upd_m a v m0 = Some m /\ Q m s) 
         Q.
Proof.
  intros. eapply HT_forall_exists. intro. eapply HT_forall_exists. 
  intro. eapply HT_forall_exists. intro. eapply HT_forall_exists. 
  intro. eapply HT_forall_exists. 
  eapply store_spec_wp. 
Qed.


(* We prove a fairly abstract characterization, which is all we will actually use
in what follows.  If we switch to a richer memory model, this triple should still hold... *)

Definition alloc := [Alloc].

Lemma rep_len: forall X (x:X) n, length (rep n x) = n. 
Proof.
  induction n ; simpl; auto. 
Qed.

Lemma rep_Z_len : forall X (x:X) z, z >= 0 -> Z_of_nat (length (rep_Z z x)) = z. 
Proof.
  intros.
  unfold rep_Z. 
  destruct (z <? 0) eqn:E. 
    rewrite <- Zlt_is_lt_bool in E.  
  omega. rewrite rep_len.  apply Z2Nat.id. omega. 
Qed.

Lemma alloc_spec_wp : forall Q : memory -> stack -> Prop,  (* the annotation on Q is crucial *)
  HT alloc
     (fun m0 s0 => exists s cnt, s0 = (cnt,handlerTag):::s /\
                                   cnt >= 0 /\
                                   (forall a m,
                                      extends m0 m -> 
                                      (forall p, a <= p < a+cnt -> ~ valid_address p m0) ->
                                      (forall p, a <= p < a+cnt -> valid_address p m) ->
                                      Q m ((a,handlerTag):::s)))
     Q.
Proof.
  intros. unfold alloc.
  unfold CodeTriples.HT. intros. destruct H0 as [s [cnt [? [? ?]]]].
  exists ((Z.of_nat (length cache0),handlerTag):::s).
  exists (cache0 ++ (rep_Z cnt (0,handlerTag))). 
  split. eapply H3. 
  unfold extends.  intros.  apply index_list_Z_app2. eauto. 
  intros. unfold valid_address. intros [P1 P2].  zify.  rewrite Z2Nat.id in P2. omega. omega. 
  intros. unfold valid_address. split. zify; omega.  rewrite app_length.  zify. 
    rewrite rep_Z_len. rewrite Z2Nat.id. zify; omega. omega.  omega. 
  
  (* Load an instruction *)
  unfold code_at in *. intuition.

  (* Run an instruction *)
  eapply rte_step; auto.
  simpl in H1.  subst. 
  eapply cstep_alloc_p; eauto.
Qed.


Lemma unpack_spec_wp : forall Q,
  HT [Unpack]
     (fun m s => exists x l s0, 
                 s = (x,l):::s0 /\ 
                 Q m ((l,handlerTag):::(x,handlerTag):::s0))
     Q.
Proof.
  intros. 
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


Lemma pack_spec_wp : forall Q,
  HT [Pack]
     (fun m s => exists x l l0 s0,
                 s = (l,handlerTag):::(x,l0):::s0 /\
                 Q m ((x,l):::s0))
     Q.
Proof.
  intros. 
  unfold CodeTriples.HT. intros. destruct H0 as [x [l [l0 [s0 [? ?]]]]].
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


(** Specifications of derived utility operations *)

Lemma loadFrom_spec: forall a v vl, forall m0 s0,
  index_list_Z a m0 = Some (v,vl) ->
  HT (loadFrom a)
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = CData (v,vl) :: s0).
Proof.
  intros.
  eapply HT_compose.
  eapply push_spec''.
  eapply load_spec.
  eauto.
Qed.

Lemma loadFrom_spec_I: forall a v vl I,
  HT (loadFrom a)
     (fun m s => index_list_Z a m = Some (v,vl) /\
                   I m s)
     (fun m s => 
        match s with 
            | CData (z,t) :: tl =>
              v = z /\ t = vl /\ I m tl
            | _ => False
        end).
Proof.
  intros. 
  eapply HT_compose.
  eapply push_spec_I.
  eapply HT_strengthen_premise.
  eapply load_spec_I with (a:= a) (vl:= vl) (v:= v) (I:= I) ; eauto.
  simpl. intros. destruct s; try solve [intuition].
  destruct c. destruct a0 as [z t].
  intuition; subst.
  inv H.
Qed.

(* This nicely illustrates the main trick for converting ghost variable form to wp form. *)
Lemma loadFrom_spec_wp : forall a (Q: memory-> stack -> Prop), 
  HT (loadFrom a)
     (fun m s => exists v vl, index_list_Z a m = Some (v,vl) /\ Q m ((v,vl):::s))
     Q.
Proof.
  intros.
  eapply HT_strengthen_premise with
     (fun m s => exists v vl m0 s0, index_list_Z a m0 = Some (v,vl) /\ m = m0 /\ s = s0 /\ Q m ((v,vl):::s0)).
  eapply HT_forall_exists. intro v. 
  eapply HT_forall_exists. intro vl. 
  eapply HT_forall_exists. intro m1. 
  eapply HT_forall_exists. intro s0. 
  eapply HT_fold_constant_premise. intro H. 
  eapply HT_consequence'. 
  eapply loadFrom_spec; eauto.  
  split_vc. 
  split_vc. subst; eauto.
  split_vc.
Qed.

Lemma storeAt_spec: forall a v vl m s,
  HT (storeAt a)
     (fun m0 s0 => m0 = m /\
                   s0 = (v,vl) ::: s /\
                   valid_address a m)
     (fun m1 s1 => s1 = s /\
                   upd_m a (v,vl) m = Some m1).
Proof.
  intros.
  eapply HT_compose.
  eapply HT_consequence'.
  eapply push_spec''.
  intuition; eauto.
  intuition; eauto.
  Focus 2. (* Eeek! *)
  eapply store_spec.
  intuition; eauto.
  jauto.
Qed.


(* NC: [valid_address a m0] implies [upd_m] succeeds *)
Lemma storeAt_spec_wp: forall a vl Q,
  forall m s,
  HT (storeAt a)
     (fun m0 s0 => s0 = vl ::: s /\
                   upd_m a vl m0 = Some m /\
                   Q m s)
     Q.
Proof.
  intros.
  eapply HT_compose.
  eapply push_spec'.
  eapply HT_strengthen_premise.
  eapply store_spec_wp.
  intuition; eauto.
  destruct s0; simpl in *.
  - false.
  - subst.
    unfold value in *.
    inversion H0; subst.
    reflexivity.
Qed.

Example store_twice_test: forall a1 a2 vl1 vl2,
  a1 <> a2 ->
  forall m s,
  valid_address a1 m ->
  valid_address a2 m ->
  HT (storeAt a1 ++ storeAt a2)
     (fun m0 s0 => m0 = m /\
                   s0 = CData vl1 :: CData vl2 :: s)
     (fun m1 s1 => s1 = s /\
                   exists m', upd_m a1 vl1 m = Some m' /\
                              upd_m a2 vl2 m' = Some m1).
Proof.
  introv Hneq Hvalid1 Hvalid2; intros.

  eapply valid_store in Hvalid1.
  destruct Hvalid1 as [m' ?]; eauto.

  eapply valid_address_upd with (m':=m') in Hvalid2.
  eapply valid_store in Hvalid2.
  destruct Hvalid2; eauto.

  eapply HT_compose_flip.
  apply storeAt_spec_wp.
  eapply HT_strengthen_premise.
  apply storeAt_spec_wp.

  intuition; subst; eauto.
  eauto.
Qed.

(** Specifications for Structured Generators *)

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
  eapply rte_step; eauto. 
  eapply cstep_branchnz_p' ; eauto. 
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
  eapply rte_step; auto.
  eapply cstep_branchnz_p' ; eauto. 
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

(* A version of [ite_spec] that restricts the effect of the condition
   code [c] to pushing one value to the stack.

   In [genApplyRule_spec] we are considering a particular memory,
   [m0], so, here it helps to make the memory a parameter. *)
Lemma ite_spec_specialized: forall v c t f Q, forall m0 s0,
  let P := fun m s => m = m0 /\ s = s0 in
  HT c (fun m s => m = m0 /\ s = s0)
       (fun m s => m = m0 /\ s = (v,handlerTag) ::: s0) ->
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

Lemma ite_spec_specialized_I: forall v c t f Q m0 I,
  let P := fun m s => m = m0 /\ I m s in
  HT c P
       (fun m s => match s with 
                       | (z,t):::tl => m = m0 /\ I m tl /\
                                       v = z /\ t = handlerTag
                       | _ => False
                   end) ->
  (v <> 0 -> HT t P Q) ->
  (v =  0 -> HT f P Q) ->
  HT (ite c t f) P Q.
Proof.
  introv HTc HZ HNZ.
  eapply ite_spec with (Pt := fun m s => v <> 0 /\ m = m0 /\ I m s)
                       (Pf := fun m s => v =  0 /\ m = m0 /\ I m s).
  eauto.
  eapply HT_fold_constant_premise; auto.
  eapply HT_fold_constant_premise; auto.

  introv Heq.
  simpl in Heq.
  destruct s; intuition.
  destruct c0; intuition.
  destruct a ; intuition; substs; eauto.
  jauto.
Qed.

Lemma ite_spec_specialized': forall v c t f Q, forall m0 s0,
  let P := fun m s => extends m0 m /\ s = s0 in
  HT c (fun m s => extends m0 m /\ s = s0)
       (fun m s => extends m0 m /\ s = (v,handlerTag) ::: s0) ->
  (v <> 0 -> HT t P Q) ->
  (v =  0 -> HT f P Q) ->
  HT (ite c t f) P Q.
Proof.
  introv HTc HZ HNZ.
  eapply ite_spec with (Pt := fun m s => v <> 0 /\ extends m0 m /\ s = s0)
                       (Pf := fun m s => v =  0 /\ extends m0 m /\ s = s0).
  eauto.
  eapply HT_fold_constant_premise; auto.
  eapply HT_fold_constant_premise; auto.

  introv Heq.
  simpl in Heq.
  jauto.
Qed.

Lemma ite_spec_specialized_I': forall v c t f Q m0 I (Hext: extension_comp I),
  let P := fun m s => extends m0 m /\ I m s in
  HT c P
       (fun m s => match s with 
                       | (z,t):::tl => extends m0 m /\ I m tl /\
                                       v = z /\ t = handlerTag
                       | _ => False
                   end) ->
  (v <> 0 -> HT t P Q) ->
  (v =  0 -> HT f P Q) ->
  HT (ite c t f) P Q.
Proof.
  introv Hext HTc HZ HNZ.
  
  eapply ite_spec with (Pt := fun m s => v <> 0 /\ extends m0 m /\ I m s)
                       (Pf := fun m s => v =  0 /\ extends m0 m /\ I m s).
  eauto.
  eapply HT_fold_constant_premise; auto.
  eapply HT_fold_constant_premise; auto.

  introv Heq.
  simpl in Heq.
  destruct s; intuition.
  destruct c0; intuition.
  destruct a ; intuition; substs; eauto.
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
                        s = CData (vc m0 s0, handlerTag) :: s0)) ->
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

  apply (HT_consequence' _ _ _ _ _ _ Hb); intuition.
  elimtype False; jauto.

  apply (HT_consequence' _ _ _ _ _ _ Hcbs); intuition.
  elimtype False; jauto.

  intuition.
  exists (vc m0 s0).
  exists handlerTag.
  exists s0.
  intuition; subst; auto.
Qed.

(*
Lemma cases_spec_step_specialized: forall c vc b cbs d P Qb Qcbs,
  (forall I,
     HT   c (fun m s => m = m0 /\ I m s)
            (fun m s => match s with 
                          | (z,t):::tl => 
                            m = m0 /\ 
                            vc m0 s0 = z /\ 
                            t = handlerTag /\ 
                            I m tl)) ->
  HT   b P Qb ->
  HT   (cases cbs d) P Qcbs ->
  (forall I,
    HT   (cases ((c,b)::cbs) d) (fun m s => m = m0 /\ I m s)
                                (fun m s => (vc m0 s0 <> 0 -> Qb m s) /\
                                            (vc m0 s0 = 0 -> Qcbs m s))).
Proof.
*)

(* XXX: move some of these defs into CodeTriples (?) *)
Definition HProp := memory -> stack -> Prop.
(* [HProp] with ghost variables *)
Definition GProp := memory -> stack -> HProp.
(* Ghost prop Hoare triple *)
 
Definition GT (c: code) (P: HProp) (Q: GProp) := 
   forall m0 s0,
     HT c 
       (fun m s => P m0 s0 /\ m = m0 /\ s = s0)
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
                           s = CData (v m0 s0, handlerTag) :: s0).

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
   exact Hcm0s0.
   apply (HT_consequence' _ _ _ _ _ _ (Hb m0 s0)); intuition.
   elimtype False; jauto.

   fold cases.
   apply (HT_consequence' _ _ _ _ _ _ (Hcbs m0 s0)); intuition.
   elimtype False; jauto.
   intuition.  jauto. 
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
      | i :: indices' =>   (genV i m0 s0 <> 0 -> genQ i m0 s0 m s) /\
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
  GT_ext c P (fun m0 s0 m s => P m0 s0 /\
                           extends m0 m /\
                           s = CData (v m0 s0, handlerTag) :: s0).
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
  eapply Hc.
  eapply HT_consequence'. 
  eapply Hb; eauto.
  intros. intuition. eapply H0.
  elimtype False; jauto.
  auto.
  auto.
  
  intros.
  destruct H as [m' [s' [HPm0s0 [Hextm0 [Hs' Hcond]]]]]. substs.
  split; eauto. 
  intuition.
  
  fold cases.
  eapply HT_consequence'.
  eapply Hcbs.
  simpl. iauto.  
  intros. intuition. 
  elimtype False; jauto.

  intuition.
  exists (vc m0 s0).
  exists handlerTag.
  exists s0.
  intuition; subst; auto.
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

(* ******* Specifications for Booleans *)

Definition ZtoBool (z:Z) :=  negb (z =? 0). 

Definition genTrue_spec  := push_spec''.
Definition genFalse_spec := push_spec''.


(* Follow from a more general [push'_spec_wp]. *)
Lemma genTrue_spec_wp: forall Q,
  HT genTrue
     (fun m s => Q m ((1,handlerTag):::s))
     Q.
Proof.
  eapply push_spec.
Qed.

Lemma genFalse_spec_wp: forall Q,
  HT genFalse
     (fun m s => Q m ((0,handlerTag):::s))
     Q.
Proof.
  eapply push_spec.
Qed.


Lemma genAnd_spec: forall b1 b2, forall m0 s0,
  HT genAnd
     (* We need [handlerTag] on [b2] because [genAnd] returns [b2] when
        [b1] is [true]. *)
     (fun m s => m = m0 /\ s = CData (boolToZ b1,handlerTag) ::
                               CData (boolToZ b2,handlerTag) :: s0)
     (fun m s => m = m0 /\ s = CData (boolToZ (andb b1 b2),handlerTag) :: s0).
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

Lemma genAnd_spec_I: forall b1 b2, forall I,
  HT genAnd
     (fun m s => 
        match s with 
          | CData (z1 ,t1) ::CData (z2,t2) :: tl =>
            z1 = boolToZ b1 /\ z2 = boolToZ b2 /\
            t1 = handlerTag /\ t2 = handlerTag /\
            I m tl
          | _ => False
        end)
     (fun m s => 
        match s with 
          | CData (z,t) :: tl =>
            z = boolToZ (andb b1 b2) /\
            t = handlerTag /\
            I m tl
          | _ => False
        end).
Proof.
  intros.
  unfold genAnd.
  destruct b1; eapply HT_strengthen_premise.
    eapply ifNZ_spec_NZ with (v:=1).
    apply nop_spec_I.
    omega.
    simpl; jauto.
    go_match. substs. 
    eexists. split ; eauto. simpl. split; eauto.

    eapply ifNZ_spec_Z with (v:=0).
    eapply HT_compose.
    eapply pop_spec_I.
    unfold genFalse.
    eapply HT_weaken_conclusion.
    eapply push_spec_I with (I:= I). go_match.
    reflexivity.
    simpl; jauto.
    go_match. substs.
    subst. 
    eexists.
     split ; eauto. simpl. split; eauto.
Qed.

Lemma genAnd_spec_wp : forall (Q:memory -> stack -> Prop),
  HT genAnd
     (fun m s => exists b1 b2 s0, s = (boolToZ b1,handlerTag):::(boolToZ b2,handlerTag):::s0 /\
                                  Q m ((boolToZ (andb b1 b2),handlerTag):::s0))
     Q.
Proof.
  intros. 
  eapply HT_strengthen_premise with
     (fun m s => exists b1 b2 s0 m0, s = (boolToZ b1,handlerTag):::(boolToZ b2,handlerTag):::s0 /\ m = m0 /\
                                     Q m0 ((boolToZ (andb b1 b2),handlerTag):::s0)).
  eapply HT_forall_exists.  intro b1. 
  eapply HT_forall_exists.  intro b2. 
  eapply HT_forall_exists.  intro s0. 
  eapply HT_forall_exists.  intro m1. 
  eapply HT_consequence'. 
  eapply genAnd_spec. 
  split_vc. 
  split_vc. subst. eauto. 
  split_vc. 
Qed.


Definition andz (z1 z2 : Z) : Z :=
  if ZtoBool z1 then z2 else 0.

Lemma genAnd_spec_general : forall v1 v2, forall m0 s0,
  HT genAnd
     (fun m s => m = m0 /\ s = (v1,handlerTag):::(v2,handlerTag):::s0)
     (fun m s => m = m0 /\ s = (andz v1 v2,handlerTag):::s0).
Proof.
  intros.
  unfold genAnd, andz.
  destruct (ZtoBool v1) eqn:E; eapply HT_strengthen_premise.
  - assert (v1 <> 0). { intro. subst. unfold ZtoBool in E. simpl in E. congruence. }
    eapply ifNZ_spec_NZ with (v:=v1); eauto.
    apply nop_spec.
  - jauto.
  - unfold ZtoBool in E. apply Bool.negb_false_iff in E.
    apply Z.eqb_eq in E.
    subst.
    eapply ifNZ_spec_Z with (v:=0); auto.
    eapply HT_compose.
    eapply pop_spec.
    eapply HT_weaken_conclusion.
    eapply push_spec_I.
    go_match. 
  - jauto. 
Qed.


Lemma genAnd_spec_general_wp : forall (Q:memory -> stack -> Prop),
  HT genAnd
     (fun m s => exists v1 v2 s0, s = (v1,handlerTag):::(v2,handlerTag):::s0 /\
                                  Q m ((andz v1 v2,handlerTag):::s0))
     Q.
Proof.
  intros. 
  eapply HT_strengthen_premise with
     (fun m s => exists v1 v2 s0 m0, s = (v1,handlerTag):::(v2,handlerTag):::s0 /\ m = m0 /\
                                     Q m0 ((andz v1 v2,handlerTag):::s0)).
  eapply HT_forall_exists.  intro v1. 
  eapply HT_forall_exists.  intro v2. 
  eapply HT_forall_exists.  intro s0. 
  eapply HT_forall_exists.  intro m1. 
  eapply HT_consequence'. 
  eapply genAnd_spec_general. 
  split_vc. 
  split_vc. subst. eauto. 
  split_vc. 
Qed.




Lemma genOr_spec: forall b1 b2, forall m0 s0,
  HT genOr
     (fun m s => m = m0 /\ s = CData (boolToZ b1,handlerTag) ::
                               CData (boolToZ b2,handlerTag) :: s0)
     (fun m s => m = m0 /\ s = CData (boolToZ (orb b1 b2),handlerTag) :: s0).
Proof.
  intros.
  unfold genOr.
  destruct b1; eapply HT_strengthen_premise.

    eapply ifNZ_spec_NZ with (v:=1).
    eapply HT_compose.
    eapply pop_spec.
    eapply HT_weaken_conclusion.
    eapply push_spec_I.
    go_match.
    omega.
    simpl; jauto.

    eapply ifNZ_spec_Z with (v:=0).
    apply nop_spec.
    reflexivity.
    simpl; jauto.
Qed.

Lemma genOr_spec_I: forall b1 b2, forall I,
  HT genOr
     (fun m s => 
        match s with 
          | CData (z1 ,t1) ::CData (z2,t2) :: tl =>
            z1 = boolToZ b1 /\ z2 = boolToZ b2 /\
            t1 = handlerTag /\ t2 = handlerTag /\
            I m tl
          | _ => False
        end)
     (fun m s => 
        match s with 
          | CData (z,t) :: tl =>
            z = boolToZ (orb b1 b2) /\
            t = handlerTag /\
            I m tl
          | _ => False
        end).
Proof.
  intros.
  unfold genOr.
  destruct b1; eapply HT_strengthen_premise.
  eapply ifNZ_spec_NZ with (v:=1).
  eapply HT_compose.
  eapply pop_spec_I.
  eapply HT_weaken_conclusion.
  eapply push_spec_I with (I:= I). go_match.
    omega.
    simpl; jauto. 
    go_match. substs. 
    eexists.
    split ; eauto. simpl. split; eauto.

    eapply ifNZ_spec_Z with (v:=0).
    apply nop_spec_I.
    reflexivity.
    simpl; jauto.
    go_match. substs.
    eexists. split ; eauto. simpl. split; eauto.
Qed.

Lemma genOr_spec_wp : forall (Q:memory -> stack -> Prop),
  HT genOr
     (fun m s => exists b1 b2 s0, s = (boolToZ b1,handlerTag):::(boolToZ b2,handlerTag):::s0 /\
                                  Q m ((boolToZ (orb b1 b2),handlerTag):::s0))
     Q.
Proof.
  intros. 
  eapply HT_strengthen_premise with
     (fun m s => exists b1 b2 s0 m0, s = (boolToZ b1,handlerTag):::(boolToZ b2,handlerTag):::s0 /\ m = m0 /\
                                     Q m0 ((boolToZ (orb b1 b2),handlerTag):::s0)).
  eapply HT_forall_exists.  intro b1. 
  eapply HT_forall_exists.  intro b2. 
  eapply HT_forall_exists.  intro s0. 
  eapply HT_forall_exists.  intro m1. 
  eapply HT_consequence'. 
  eapply genOr_spec. 
  split_vc. 
  split_vc. subst. eauto. 
  split_vc. 
Qed.


Definition orz (z1 z2 : Z) : Z :=
  if ZtoBool z1 then 1 else z2.                      

Lemma genOr_spec_general : forall v1 v2, forall m0 s0,
  HT genOr
     (fun m s => m = m0 /\ s = (v1,handlerTag):::(v2,handlerTag):::s0)
     (fun m s => m = m0 /\ s = (orz v1 v2,handlerTag):::s0).
Proof.
  intros.
  unfold genOr, orz.
  destruct (ZtoBool v1) eqn:E; eapply HT_strengthen_premise.
  - assert (v1 <> 0). { intro. subst. unfold ZtoBool in E. simpl in E. congruence. }
    eapply ifNZ_spec_NZ with (v:=v1); eauto.
    eapply HT_compose.
    eapply pop_spec.
    eapply HT_weaken_conclusion.
    eapply push_spec_I.
    go_match. 
  - jauto. 
  - unfold ZtoBool in E. apply Bool.negb_false_iff in E.
    apply Z.eqb_eq in E.
    subst.
    eapply ifNZ_spec_Z with (v:=0); auto.
    apply nop_spec.
  - jauto.
Qed.

Lemma genOr_spec_general_wp : forall (Q:memory -> stack -> Prop),
  HT genOr
     (fun m s => exists v1 v2 s0, s = (v1,handlerTag):::(v2,handlerTag):::s0 /\
                                  Q m ((orz v1 v2,handlerTag):::s0))
     Q.
Proof.
  intros. 
  eapply HT_strengthen_premise with
     (fun m s => exists v1 v2 s0 m0, s = (v1,handlerTag):::(v2,handlerTag):::s0 /\ m = m0 /\
                                     Q m0 ((orz v1 v2,handlerTag):::s0)).
  eapply HT_forall_exists.  intro v1. 
  eapply HT_forall_exists.  intro v2. 
  eapply HT_forall_exists.  intro s0. 
  eapply HT_forall_exists.  intro m1. 
  eapply HT_consequence'. 
  eapply genOr_spec_general. 
  split_vc. 
  split_vc. subst. eauto. 
  split_vc. 
Qed.


Lemma genNot_spec_general: forall v, forall m0 s0,
  HT genNot
     (fun m s => m = m0 /\ s = CData (v, handlerTag) :: s0)
     (fun m s => m = m0 /\ 
                 s = CData (boolToZ (v =? 0),handlerTag) :: s0).
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

Lemma genNot_spec_general_I: forall v, forall I,
  HT genNot
     (fun m s => match s with 
                   | (z, t) ::: tl =>
                     v = z /\ t = handlerTag /\ I m tl
                   | _ => False
                 end)
     (fun m s => match s with 
                   | (z,t) ::: tl =>
                     boolToZ (v =? 0) = z /\ t = handlerTag /\ I m tl
                   | _ => False
                 end).
Proof.
  intros.
  unfold genNot.
  cases (v =? 0) as Heq.
  - apply Z.eqb_eq in Heq.
    eapply HT_strengthen_premise.
    + eapply ifNZ_spec_Z.
      * eapply HT_weaken_conclusion. eapply push_spec_I with (I:= I).
        go_match. 
      * eauto.
    + go_match. 
  - apply Z.eqb_neq in Heq.
    eapply HT_strengthen_premise.
    + eapply ifNZ_spec_NZ.
      * eapply HT_weaken_conclusion. eapply push_spec_I with (I:= I).
        go_match. 
      * eauto.
    + go_match. 
Qed.

Lemma genNot_spec: forall b, forall m0 s0,
  HT genNot
     (fun m s => m = m0 /\ s = (boolToZ b, handlerTag) ::: s0)
     (fun m s => m = m0 /\ s = (boolToZ (negb b), handlerTag) ::: s0).
Proof.
  intros.
  eapply HT_weaken_conclusion.
  - eapply genNot_spec_general.
  - cases b; auto.
Qed.

Lemma genImpl_spec: forall b1 b2, forall m0 s0,
  HT genImpl
     (fun m s => m = m0 /\ s = CData ((boolToZ b1),handlerTag) ::
                               CData ((boolToZ b2),handlerTag) :: s0)
     (fun m s => m = m0 /\ s = CData ((boolToZ (implb b1 b2)),handlerTag) :: s0).
Proof.
  intros.
  eapply HT_weaken_conclusion.
  unfold genImpl.
  eapply HT_compose.
  eapply genNot_spec.
  eapply genOr_spec.
  simpl. cases b1; cases b2; iauto.
Qed.

Lemma genImpl_spec_wp:  forall Q : memory -> stack -> Prop,
  HT genImpl
     (fun (m : memory) (s : stack) =>
        exists b1 b2 s0,
          s = (boolToZ b1, handlerTag) ::: (boolToZ b2, handlerTag) ::: s0 /\
          Q m ((boolToZ (implb b1 b2), handlerTag) ::: s0)) Q.
Proof.
  intros. 
  unfold genImpl.
  eapply HT_compose_flip.
  eapply genOr_spec_wp; eauto.
  unfold genNot.
  eapply HT_strengthen_premise.
  eapply ifNZ_spec_existential.
  eapply genFalse_spec_wp.
  eapply genTrue_spec_wp.
  split_vc. substs.
  split; intros.
  unfold implb, orb in *.
  exists (negb x); exists x0. exists x1.
  intuition; eauto;
  (repeat f_equal; eauto; (destruct x; simpl in *; try congruence)). 
  exists (negb x); exists x0. exists x1.
  intuition; eauto;
  (repeat f_equal; eauto; (destruct x; simpl in *; try congruence)). 
Qed.

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


Lemma genEq_spec: forall v1 v2 m0 s0,
  HT genEq
     (fun m s => m = m0 /\ s = (v1,handlerTag):::(v2,handlerTag):::s0) 
     (fun m s => m = m0 /\ s = (boolToZ(v1 =? v2),handlerTag):::s0).
Proof.
  intros. unfold genEq.
  eapply HT_compose.
  eapply sub_spec. 
  eapply HT_consequence. 
  eapply genNot_spec_general with (v:=v1-v2). 
  intros. jauto.
  simpl. intros. intuition jauto. 
  rewrite basic_arithmetic in H1. rewrite Z.eqb_sym. auto.
Qed.

Lemma genEq_spec_wp : forall Q : memory -> stack -> Prop,
  HT genEq
     (fun m s => exists v1 v2 m0 s0 , 
                                  m = m0 /\ (* tedious trick again *)
                                  s = (v1,handlerTag):::(v2,handlerTag):::s0 /\
                                  Q m0 ((boolToZ(v1 =? v2),handlerTag):::s0))
     Q.
Proof.
  intros.
  eapply HT_forall_exists. intro v1. 
  eapply HT_forall_exists. intro v2. 
  eapply HT_forall_exists. intro m0. 
  eapply HT_forall_exists. intro s0. 
  eapply HT_consequence'.
  eapply genEq_spec; eauto.  
  intros. simpl. jauto. 
  intros. destruct H as [m' [s' [? [? ?]]]]. simpl in H0. destruct H0. subst.  auto.
Qed.


(* NC: use [Z.eqb_eq] and [Z.eqb_neq] to relate the boolean equality
   to propositional equality. *)
Lemma genTestEqual_spec: forall c1 c2, forall v1 v2, forall m0,
  (forall s0,
     HT c1
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (v1,handlerTag) ::: s0)) ->
  (forall s0,
     HT c2
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (v2,handlerTag) ::: s0)) ->
  (forall s0,
     HT (genTestEqual c1 c2)
        (fun m s => m = m0 /\ s = s0)
        (fun m s => m = m0 /\ s = (boolToZ (v1 =? v2),handlerTag) ::: s0)).
Proof.
  intros.
  unfold genTestEqual.
  eapply HT_compose; eauto.
  eapply HT_compose; eauto.
  eapply HT_compose.
  eapply sub_spec.
  eapply HT_weaken_conclusion.
  eapply genNot_spec_general.


  rewrite basic_arithmetic in *; intuition.
Qed.

Lemma genTestEqual_spec_I: forall c1 c2, forall v1 v2, forall m0,
  (forall I (Hext: extension_comp I),
     HT c1
        (fun m s => extends m0 m /\ I m s)
        (fun m s => match s with 
                        | (z1,t):::tl => 
                          v1 = z1 /\ extends m0 m /\ t = handlerTag /\ I m tl
                        | _ => False
                    end)) ->
  (forall I (Hext: extension_comp I),
     HT c2
        (fun m s => extends m0 m /\ I m s)
        (fun m s => match s with 
                      | (z2,t)::: tl => 
                        extends m0 m /\ v2 = z2 /\ t = handlerTag /\ I m tl
                      | _ => False
                    end)) ->
  (forall I (Hext: extension_comp I),
     HT (genTestEqual c1 c2)
        (fun m s => extends m0 m /\ I m s)
        (fun m s => match s with 
                      | (z,t)::: tl => 
                        extends m0 m /\ boolToZ (v1 =? v2) = z /\
                        t = handlerTag /\
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
                       z1 = v1 /\ t1 = handlerTag /\
                       I m tl /\ extends m0 m
                     | _ => False
                   end).
  unfold extension_comp, extends.
  intros; intuition. go_match.
  go_match.
  eapply HT_compose.
  eapply HT_strengthen_premise. 
  eapply sub_spec_I with (I:= fun m s => extends m0 m /\ I m s).
  go_match. 
  eapply HT_weaken_conclusion.
  eapply HT_strengthen_premise.
  eapply (genNot_spec_general_I (v2-v1)) with (I:= fun m s => extends m0 m /\ I m s).
  go_match.
  go_match.
  rewrite basic_arithmetic in *; intuition.
Qed.

(*** Specifications for Options *)

(* NC: this might be a way to do "transformer" style ... *)
Lemma some_spec: forall c, forall m0 s0 s1,
  HT c 
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = s1) ->
  HT (some c)
     (fun m s => m = m0 /\ s = s0)
     (fun m s => m = m0 /\ s = (1,handlerTag) ::: s1).
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
            | (1,t) ::: tl => t = handlerTag /\ Q m tl
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


(* ********* Specifications for loops **************** *)

(* Several different versions of the spec. *)
Lemma loopNZ_spec'': forall c I,
(forall n, (0 < n)%nat ->
  HT c
     (fun m s => exists i s', s = CData (i,handlerTag) :: s' /\ I m s /\ i = Z_of_nat n)
     (fun m s => exists i' s', s = CData (i',handlerTag) :: s' /\ I m (CData (i',handlerTag) :: s') /\ i' = Z_of_nat (pred n))) -> 
(forall n, (0 < n)%nat -> 
  HT (loopNZ c)
     (fun m s => exists i s', s = CData (i,handlerTag) :: s' /\ I m s /\ i = Z_of_nat n)
     (fun m s => exists s', s = CData (0,handlerTag) :: s' /\ I m s)).
Proof.
  intros c I P. 
  unfold loopNZ, dup. 
  intros n H.  generalize dependent n. 
  induction n. 
  intros.  inversion H. 
  unfold CodeTriples.HT in *. intros.
  destruct H1 as [i [s' [P1 [P2 P3]]]].

  edestruct P as [stk1 [cache1 [[i' [s'' [Q1 [Q2 Q3]]]] Q4]]].
  eapply H. eapply code_at_compose_1; eauto.
  eexists. eexists. split. eauto. eauto. eauto. 
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
    eexists. eexists. split. eexists. split. eauto. eauto. 
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
  edestruct IHn as [stk3 [cache3 [[s''' [R1 R2]] R3]]]. 
  zify; omega.
  eauto.
  eexists (Z_of_nat n).  eexists s''.  eauto. eauto.
  eexists.  eexists. split. eexists. split. eauto. eauto. 
  subst. 
  eapply runsToEnd_trans. 
  eapply Q4.  clear Q4. 
  repeat rewrite app_length in *. simpl in R3.
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
     (fun m s => exists s', s = CData (i,handlerTag) :: s' /\ I m s)
     (fun m s => exists i' s', s = CData (i',handlerTag) :: s' /\ I m (CData (i',handlerTag) :: s') /\ i' = Z.pred i)) -> 
(forall i, 0 < i -> 
  HT (loopNZ c)
     (fun m s => exists s', s = CData (i,handlerTag) :: s' /\ I m s)
     (fun m s => exists s', s = CData (0,handlerTag) :: s' /\ I m s)).
Proof.
  intros c I P. 
  unfold loopNZ, dup. 
  intros i H.  assert (0 <= i) by omega. generalize dependent H. 
  set (Q := fun i => 0 < i ->
   HT (c ++ [Dup 0] ++ [BranchNZ (- Z.of_nat (length (c ++ [Dup 0])))])
     (fun (m : memory) (s : stack) => exists s', s = (i, handlerTag) ::: s' /\ I m s)
     (fun (m : memory) (s : stack) => exists s', s = (0, handlerTag) ::: s' /\ I m s)).
  pattern i. fold Q. 
  generalize dependent i. 
  eapply natlike_ind; unfold Q; clear Q. 
  intros.  inversion H. 
  unfold CodeTriples.HT in *. intros i E1 IH E2.
  intros. 
  destruct H0 as [s' [P1 P2]].

  edestruct P as [stk1 [cache1 [[i' [s'' [Q1 [Q2 Q3]]]] Q4]]].
  eauto. 
  eapply code_at_compose_1; eauto.
  eexists. split. eauto. subst stk0.  eauto. eauto. 
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
  eexists. eexists. split. eexists. split. eauto. eauto.
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
  edestruct IH as [stk3 [cache3 [[s''' [R1 R2]] R3]]]. 
  zify; omega. 
  eauto.
  exists s''.  eauto. eauto.
  eexists.  eexists. split. eexists. split. eauto. eauto. 
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
     (fun m s => exists s', s = CData (i,handlerTag) :: s' /\ I m s)
     (fun m s => exists i' s', s = CData (i',handlerTag) :: s' /\ I m (CData (i',handlerTag) :: s') /\ 0 <= i' < i)) -> 
(forall i, 0 < i -> 
  HT (loopNZ c)
     (fun m s => exists s', s = CData (i,handlerTag) :: s' /\ I m s)
     (fun m s => exists s', s = CData (0,handlerTag) :: s' /\ I m s)).
Proof.
  intros c I P. 
  unfold loopNZ, dup. 
  intros i H.  assert (0 <= i) by omega. generalize dependent H. 
  set (Q := fun i => 0 < i ->
   HT (c ++ [Dup 0] ++ [BranchNZ (- Z.of_nat (length (c ++ [Dup 0])))])
     (fun (m : memory) (s : stack) => exists s', s = (i, handlerTag) ::: s' /\ I m s)
     (fun (m : memory) (s : stack) => exists s', s = (0, handlerTag) ::: s' /\ I m s)).
  pattern i. fold Q. 
  generalize dependent i. 
  eapply Zlt_0_ind; unfold Q; clear Q. 
  intros i.  
  unfold CodeTriples.HT in *. intros. 
  destruct H3 as [s' [P1 P2]].

  edestruct P as [stk1 [cache1 [[i' [s'' [Q1 [Q2 Q3]]]] Q4]]].
  eauto. 
  eapply code_at_compose_1; eauto.
  eexists. split. eauto. subst stk0.  eauto. eauto. 
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
  eexists. eexists. split. eexists. split. eauto. eauto.
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
  edestruct H as [stk3 [cache3 [[s''' [R1 R2]] R3]]]. 
  instantiate (1:= i').  omega. 
  zify; omega.
  eauto.
  exists s''.  eauto. eauto.
  eexists.  eexists. split. eexists. split. eauto. eauto. 
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
     (fun m s => exists s', s = CData(i,handlerTag)::s' /\ I m s) 
     (fun m s => exists s', s = CData(i,handlerTag)::s' /\ I m (CData(Z.pred i,handlerTag)::s'))) ->
  (forall i, 0 <= i -> 
  HT (genRepeat c) 
     (fun m s => exists s', s = CData(i,handlerTag)::s' /\ I m s)
     (fun m s => exists s', s = CData(0,handlerTag)::s' /\ I m s)).
Proof.
  intros c I P. 
  unfold genRepeat. 
  intros i H.
  eapply HT_compose with (Q:= (fun m s => exists s', s = (i,handlerTag) ::: (i,handlerTag) ::: s' /\ I m ((i,handlerTag):::s'))). 
  eapply HT_strengthen_premise.
  eapply dup_spec_wp. 
  intros m s [s' [H1 H2]]. 
  eexists. split.  simpl. rewrite H1; auto.
  subst s. eexists. intuition eauto. 
  (* oh gee whiz. this is unbelievably painful. *)
  set (Q := fun i m s' => exists s'', s' = (i,handlerTag):::s'' /\ I m s' /\ i > 0). 
  set (Q0 := fun m s' => exists s'', s' = (0,handlerTag):::s'' /\ I m s').
  eapply HT_strengthen_premise with (fun m s => exists s', s = (i,handlerTag)::: s' /\
                                           (i <> 0 -> Q i m s') /\
                                           (i = 0 -> Q0 m s')).
  eapply ifNZ_spec. 
  destruct (Z.eq_dec i 0). unfold CodeTriples.HT. intros. destruct H1 as [s'' [_ [_ CONTRA]]].  exfalso; omega. 
  eapply HT_strengthen_premise.
  eapply loopNZ_spec. 
  3: intros m s [s'' [P1 [P2 P3]]]; eexists; intuition eauto. 
  2: omega. 
  intros. 
  eapply HT_compose. 
  apply P; auto.
  eapply HT_compose. 
  eapply push_spec'.

  eapply HT_strengthen_premise.
  eapply add_spec_wp'. 
  simpl. intros m s [R1 [s' [R2 R3]]]. 
  eexists. eexists. eexists.
  split. destruct s. inv R1. inv R1. simpl in R2. subst s. eauto. 
  eexists. eexists. split. eauto.
  split. replace (-1 + i0) with (Z.pred i0) by omega. auto. omega. 

  eapply HT_strengthen_premise.
  eapply nop_spec_wp. 
  intros. destruct H0 as [s'' [P1 P2]]. eexists.  intuition eauto. 

  intros m s [s' [P1 P2]]. eexists. split. eauto.  split.
  intros. unfold Q. eexists. split. eauto. split. eauto.  omega. 
  intros. unfold Q0. eexists. split. eauto. subst i. eauto. eauto.
Qed.


Lemma genRepeat_spec': forall c I,
  (forall i, 0 < i -> 
  HT c 
     (fun m s => exists s', s = CData(i,handlerTag)::s' /\ I m s) 
     (fun m s => exists s', s = CData(i,handlerTag)::s' /\ I m (CData(Z.pred i,handlerTag)::s'))) ->
  HT (genRepeat c) 
     (fun m s => exists i s', 0 <= i /\ s = CData(i,handlerTag)::s' /\ I m s)
     (fun m s => exists s', s = CData(0,handlerTag)::s' /\ I m s).
Proof.
  intros c I P. 
  
  eapply HT_forall_exists. intro i.
  eapply HT_forall_exists. intro s'.
  eapply HT_fold_constant_premise. intro.
  generalize s'. 
  eapply HT_exists_forall. 
  eapply genRepeat_spec; eauto. 
Qed.


(* *** HTEscape specifications *)

Lemma ret_specEscape: forall raddr (P: memory -> stack -> Prop),
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

Lemma vret_specEscape: forall raddr (P: memory -> stack -> Prop),
  HTEscape raddr [VRet]
    (fun m s => exists s' s'' res, c_pop_to_return s' ((CRet raddr true false)::s'') /\
                               s = res:::s' /\ P m (res:::s''))
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
  destruct x1. 
  eapply cstep_vret_p; auto.
Qed.

Lemma jump_specEscape_Failure: forall raddr (P: memory -> stack -> Prop),
  HTEscape raddr [Jump]
           (fun m s => exists s0, (-1, handlerTag) ::: s0 = s /\ P m s0)
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
           (fun m s => exists s0, s = (v, handlerTag) ::: s0 /\
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
           (fun m s => exists s0, s = (v, handlerTag) ::: s0 /\
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

Ltac apply_wp :=
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


(* We probably won't need this stuff...
   In any case it needs revision in light of what we learned doing the above. 

Definition genRepeatUntil (c:code) :=
  let c' := c ++ swap ++ push' (-1) ++ [Add] ++ swap in
  let c'' := c' ++ dup ++ skipNZ 3 ++ pop ++ dup in
  push' 0 ++
  skip (length c') ++
  loopNZ c''.

(* maybe redo with B as decidable prop, not boolean *)
Conjecture genRepeatUntil_spec: forall c I B,
  (forall i il, i > 0 -> 
   HT c
      (fun m s => exists s', s = CData(i,il)::s' /\ I m s /\ B m s = false)
      (fun m s => exists b bl s', s = CData(b,bl)::CData(i,il)::s' /\ I m (** adjust **) s /\  b = boolToZ (B m (CData(i,il)::s')))) ->
   HT (genRepeatUntil c)
      (fun m s => exists b bl i il s', s = CData(b,bl)::CData(i,il)::s' /\ I m s /\ b = boolToZ(B m (CData(i,il)::s')) /\ i >= 0)
      (fun m s => exists b bl i il s', s = CData(b,bl)::CData(i,il)::s' /\ I m s /\ b = boolToZ(B m (CData(i,il)::s')) /\ i >= 0 /\ (i = 0 \/ b <> 0)).

*)


