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
Require Import CLattices.


Local Open Scope Z_scope. 

Section SOP.

(* DD: A simpler definition would be 
   labtoz l z m := memarr m z l
   But this is to much constraint. Indeed, memarray can contain 
   duplicates. *) 
Definition labToZ (l: Zset.t) (z: Z) (m: list (@Atom Z)) : Prop := 
  exists c,
    memarr m z c /\
    (forall a, In a c <-> Zset.In a l) /\
    (mem_def_on_cache m -> z > 6). 

Lemma mem_eq_except_cache_memseq: forall m m' z x,
  mem_eq_except_cache m m' ->
  z > 6 ->
  memseq m z x->
  memseq m' z x.
Proof.
  intros.
  inv H. inv H2.
  destruct H as [tagPC [tag1 [tag2 [tag3 [tagr [tagrpc Hhit]]]]]].
  intuition.
  gdep z;  gdep x.
  induction x; intros.
  constructor; eauto.
  inv H1. econstructor; eauto.
  apply (H3 z) in H12; eauto;
  (unfold addrOpLabel, addrTagPC, 
                             addrTag1, addrTag2, addrTag3, 
                             addrTagRes, addrTagResPC; zify ; omega).
  eapply IHx; eauto.
  zify; omega.
Qed.

Lemma labToZ_cache_SOP: forall l z m m', 
                          labToZ l z m -> mem_eq_except_cache m m' -> labToZ l z m'.
Proof.
  intros.
  inv H0. inv H1. destruct H0 as [tagPC [tag1 [tag2 [tag3 [tagr [tagrpc Hhit]]]]]].
  intuition.
  unfold labToZ in *.
  inv H. exists x0. 
  assert (Hmem: mem_def_on_cache m) by (econstructor; eauto ; do 6 eexists; intuition ; eauto).
  intuition.
  inv H. econstructor; eauto.
  erewrite <- H2; eauto;
  (unfold addrOpLabel, addrTagPC, 
                             addrTag1, addrTag2, addrTag3, 
                             addrTagRes, addrTagResPC; zify ; omega).
  eapply mem_eq_except_cache_memseq; eauto. econstructor; eauto. zify ; omega.
Qed.
  
Lemma memseq_extension_comp : forall m1 m2 l z,
  memseq m1 z l ->
  extends m1 m2 ->
  memseq m2 z l.
Proof.
  induction l ; intros.
  constructor. 
  inv H.
  constructor; auto. 
Qed.

Lemma labToZ_extension_comp_SOP : 
  forall m1 m2 l z,  
    labToZ l z m1 -> extends m1 m2 -> mem_def_on_cache m1 -> labToZ l z m2.
Proof.
  unfold labToZ. intros.
  inv H. intuition.
  exists x. intuition. 
  inv H.
  econstructor; auto. 
  eapply H0. auto.
  eapply memseq_extension_comp; eauto.
Qed.

Fixpoint acc_content_list (l: nat) (z: Z) (m: list (@Atom Z)) (s: list Z) := 
  match l with 
      | O => s 
      | S n => 
        match read_m z m with 
          | Some (e,_) => acc_content_list n (z+1) m (e::s)
          | None => acc_content_list n (z+1) m s
        end
  end.

Definition ZToLab (z: Z) (m: list (@Atom Z)) : Zset.t :=
  match read_m z m with 
    | None => Zset.empty
    | Some (l,_) => fold_left (fun acc e => Zset.add e acc)
                              (acc_content_list (Z.to_nat l) (z+1) m nil)
                              Zset.empty
  end.

Definition genFlows : list Instr := subset_arrays.

Definition genBot : list Instr := push 0 ++ alloc_array.
Definition genJoin : list Instr := concat_arrays. 

Global Instance SOPClatt : ConcreteLattice Zset.t :=
{ labToZ := labToZ 
; ZToLab := ZToLab
; genBot := genBot
; genJoin:= genJoin
; genFlows:= genFlows
}.

Lemma memseq_incl : forall m l1 l2 z, 
 memseq m z l1 -> 
 length l1 = length l2 ->
 memseq m z l2 -> incl l1 l2.
Proof.
  induction l1 ; intros. 
  - inv H. inv H1. unfold incl. auto. inv H0. 
  - inv H. destruct l2. inv H0.  inv H0.
    unfold incl. intros. inv H.
    inv H1. allinv'. constructor. auto.
    exploit (IHl1 l2 (z+1)); eauto. inv H1; auto.
    intros. constructor 2; auto.
Qed.                               

Lemma labToZ_inj_SOP : forall l1 l2 z m, labToZ l1 z m -> labToZ l2 z m -> l1 = l2.
Proof.
  unfold labToZ. intros.
  destruct H as [c1 [Hl1 Hinl1]]. inv Hl1.
  destruct H0 as [c2 [Hl2 Hinl2]]. inv Hl2.

  assert (Hc1c2: incl c1 c2).
  eapply memseq_incl; eauto. allinv'. 
  eapply Nat2Z.inj_iff in H4. auto.

  assert (Hc2c1: incl c2 c1).
  eapply memseq_incl; eauto. allinv'. 
  eapply Nat2Z.inj_iff in H4. auto.

  
  eapply Zset.antisym; eapply Zset.incl_spec.

  unfold incl. intros.
  unfold Zset.In in *. 
  eapply Hinl2. eapply Hc1c2. eapply Hinl1. auto.

  unfold incl. intros.
  unfold Zset.In in *. 
  eapply Hinl1. eapply Hc2c1. eapply Hinl2. auto.
Qed.

Lemma fold_left_add_helper1 : forall l S,
  forall x, Zset.In x S -> Zset.In x (fold_left (fun acc e => Zset.add e acc) l S). 
Proof.
  induction l ; intros.
  simpl. auto.
  simpl. eapply IHl; eauto.
  eapply Zset.In_add. eauto.
Qed.

Lemma fold_left_add_helper2 : forall l S,
  forall x, In x l -> Zset.In x (fold_left (fun acc e => Zset.add e acc) l S). 
Proof.
  induction l ; intros.
  inv H.
  simpl. inv H.
  eapply fold_left_add_helper1; eauto.
  eapply Zset.In_add; eauto.
  eapply IHl; eauto.
Qed.

Lemma fold_left_add_complete : forall l S S', 
                                (forall a, In a l <-> Zset.In a S') ->
                                Zset.incl (Zset.union S' S)
                                          (fold_left (fun acc e => Zset.add e acc) l S)
                                           = true.
Proof.
  intros.
  eapply Zset.incl_spec.
  intros x Hinx.
  eapply Zset.In_union in Hinx.
  inv Hinx. 
  eapply H in H0.
  eapply fold_left_add_helper2; auto.
  eapply fold_left_add_helper1; auto.
Qed.

Lemma fold_left_add_helper3 : forall l S,
  forall x, Zset.In x (fold_left (fun acc e => Zset.add e acc) l S) -> Zset.In x S \/ In x l.
Proof.
  induction l ; intros.
  simpl in *. auto.
  simpl in *. 
  exploit IHl; eauto. intros [Hinadd1 | Hinadd2].
  - eapply Zset.In_add in Hinadd1. intuition. 
  - intuition.
Qed.

Lemma fold_left_add_correct : forall l S' S, 
                                (forall a, In a l <-> Zset.In a S') ->
                                Zset.incl (fold_left (fun acc e => Zset.add e acc) l S)
                                          (Zset.union S' S) = true.
Proof.
  intros. eapply Zset.incl_spec.
  intros x Hinx.
  eapply Zset.In_union. 
  exploit fold_left_add_helper3; eauto. intros [Hcase1 | Hcase2].
  eauto.
  left; eauto. eapply H; auto.
Qed.    

Lemma acc_content_list_memseq_correct : forall m vs z,
  memseq m z vs ->            
  forall l,
  acc_content_list (length vs) z m l = (rev vs)++l. 
Proof.
  induction 1; intros;  auto.
  simpl. rewrite H.
  erewrite IHmemseq; eauto.
  rewrite <- app_assoc.
  reflexivity.
Qed.
  
Lemma zfset_union_empty : forall S, Zset.union S Zset.empty = S.
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
    
Lemma labToZ_ZToLab_id_SOP : forall l z m, labToZ l z m -> ZToLab z m = l.
Proof.
  unfold labToZ, ZToLab ; intros. 
  destruct H as [vs [Hmemarr [Hvsl Hmemdef]]].
  inv Hmemarr. rewrite H. rewrite Nat2Z.id.
  assert (Hvsl' : forall a, In a (rev vs) <-> Zset.In a l).
  { split; intros. eapply Hvsl. eapply in_rev; auto.
    rewrite <- in_rev; auto. eapply Hvsl; auto. }  
  eapply Zset.antisym;
    (erewrite acc_content_list_memseq_correct; auto);
    (rewrite app_nil_r);
    (replace l with (Zset.union l Zset.empty) by (rewrite <- zfset_union_empty; auto)).
  - eapply fold_left_add_correct; eauto.    
  - eapply fold_left_add_complete; eauto.
Qed.
    
Lemma mem_def_on_cache_valid_address : forall m a,
                                         mem_def_on_cache m ->
                                         0 <= a <= 6 ->
                                         valid_address a m.
Proof.
  intros.
  intros. destruct H as [op [pctag [tag1 [tag2 [tag3 [tagr [tagrpc Hint]]]]]]].
  intuition.
  econstructor; eauto.
  inv H8. unfold addrTagResPC in *.
  eapply index_list_Z_valid in H7; eauto.
  intuition. 
  assert (Z.to_nat a <= Z.to_nat 6)%nat.
  eapply Z2Nat.inj_le; eauto.
  eauto with arith. 
Qed.

Section syscall.
Context {T:Type}.
Variable SysTable : syscall_table T.

Lemma genBot_spec_SOP : forall m0 (Hm0: mem_def_on_cache m0) (Q:memory->stack->Prop),
   HT SysTable genBot
      (fun m s => extends m0 m /\ 
                  (forall m1 z, 
                     extends m m1 -> labToZ bot z m1 -> Q m1 ((z,handlerTag):::s)))
      Q.
Proof.
  intros.
  eapply HT_compose_flip.
  eapply alloc_array_spec_wp; eauto. 
  eapply HT_strengthen_premise.
  eapply push_spec_wp; eauto.
  split_vc. eapply (H0 m1); eauto. 
  exists (@nil Z). split. 
  econstructor; eauto.
  simpl; eauto. constructor; auto.
  split.
  unfold Zset.In. rewrite Zset.elements_empty.
  intuition. intros. 
  { destruct (Z_le_dec a 6).
    - eelim (H2 a); eauto. omega.
      eapply mem_def_on_cache_valid_address; eauto.
      inv H5. 
      exploit index_list_Z_valid; eauto.  omega. 
    - omega. 
  }  
Qed.

Lemma memseq_prefix: forall m a vs'',
                       memseq m a vs'' ->
                       forall vs vs',
                         (vs++vs') = vs'' ->
                         memseq m a vs.
Proof.
  induction 1; intros.
  eapply app_eq_nil in H.
  inv H. constructor; auto.
  destruct vs0. simpl in *.
  destruct vs'. inv H1.
  inv H1. constructor; auto.
  simpl in H1. inv H1.
  constructor; auto.
  eapply IHmemseq; eauto.
Qed.

Lemma genJoin_spec_SOP: forall m0 (Hm0: mem_def_on_cache m0) (Q: memory-> stack->Prop),
       HT SysTable genJoin
         (fun m s =>
          exists s0 l z l' z',
             s = (z, handlerTag) ::: (z', handlerTag) ::: s0 /\
             extends m0 m /\
             labToZ l z m /\ labToZ l' z' m /\
             (forall m1 zz', extends m m1 -> labToZ (l \_/ l') zz' m1 ->
                         Q m1 ((zz', handlerTag) ::: s0)))
         Q.
Proof.
  intros. 
  eapply HT_strengthen_premise.
  eapply concat_arrays_spec_wp ; eauto.
  go_match. 
  destruct H as [s0 [l [z [l' [z' Hint]]]]]. inv Hint. intuition.
  unfold labToZ in *. 
  destruct H0 as [zl Hint1].
  destruct H1 as [zl' Hint2].
  intuition.
  do 5 eexists; eauto. intuition; eauto.
  eapply H3; eauto. 
  eexists. split; eauto.
  unfold Zset.In. split.
  { split ;intros.
  - eapply Zset.In_union. 
    exploit in_app_or; eauto. intuition.
    right. eapply H1; auto.
    left. eapply H5; auto.
  - intros. eapply Zset.In_union in H10; eauto. 
    eapply in_or_app.
    intuition.
    right. apply H5. auto. 
    left. eapply H1; auto.
  }
  exploit extends_mem_def_on_cache; eauto.
  intuition. 
  destruct H8 as [cnt [Hcnt Hinvalid]].
  { destruct (Z_le_dec r 6).
    - eelim (Hinvalid r); eauto. omega.
      eapply mem_def_on_cache_valid_address; eauto.
      inv H9. 
      exploit index_list_Z_valid; eauto.  intuition omega. 
    - omega. 
  }
Qed.
  
Lemma incl_Z_list_subset_b : forall l1 l2, 
                               incl l1 l2 <->
                               Z_list_subset_b l1 l2 = true.
Proof.
  intros. split.
  - intros. eapply forallb_forall. intros.
    eapply H in H0.  eapply existsb_exists. 
    exists x; intuition.
    eapply Z.eqb_refl. 
  - intros. 
    unfold incl. intros.
    unfold Z_list_subset_b in H. 
    eapply forallb_forall in H; eauto.
    unfold Z_list_in_b in H. 
    eapply existsb_exists in H. 
    destruct H. intuition.
    rewrite Z.eqb_compare in H2. 
    cases (a ?= x) ; try congruence.
    rewrite Z.compare_eq_iff in Eq. substs.
    auto.
Qed.

Lemma Zsetincl_Z_list_subset : forall l l' x x' b,
                               forall (Hxl : forall a, In a x <-> Zset.In a l)
                                      (Hx'l' : forall a, In a x' <-> Zset.In a l'),
                                 Zset.incl l l' = b <->
                                 Z_list_subset_b x x' = b.
Proof.
  intros. split; intros.
  - destruct b.
    apply Zset.incl_spec in H. 
    eapply incl_Z_list_subset_b; eauto.
    unfold incl, Zset.In in *. intros; eauto.
    apply Hx'l'. apply H. apply Hxl. auto.

    cases (Z_list_subset_b x x'); auto.
    eapply incl_Z_list_subset_b in Eq; eauto.
    assert (Zset.incl l l' = true).
    apply Zset.incl_spec.  
    unfold incl, Zset.In in *. intros; eauto.
    apply Hx'l'. apply Eq. apply Hxl. auto.
    congruence.

  - destruct b.
    apply Zset.incl_spec. 
    eapply incl_Z_list_subset_b in H; eauto.
    unfold incl; intros.  eapply Hx'l'. eapply H. eapply Hxl; auto.
    
    cases (Zset.incl l l'); auto.
    eapply Zset.incl_spec in Eq.
    unfold incl in Eq. 
    assert (Z_list_subset_b x x' = true).
    eapply incl_Z_list_subset_b. 
    unfold incl, Zset.In in *. intros.
    apply Hx'l'. apply Eq. apply Hxl. auto.
    congruence.
Qed.
  
Lemma genFlows_spec_SOP: forall m0 (Hm0: mem_def_on_cache m0) (Q: memory -> stack -> Prop),
                   HT SysTable genFlows
                       (fun m s =>
                          exists l l' z z' s0,
                            extends m0 m /\
                            labToZ l z m /\ labToZ l' z' m /\
                            s = (z,handlerTag):::(z',handlerTag):::s0 /\
                            Q m ((boolToZ(flows l l'),handlerTag):::s0))
                       Q.
Proof.
  intros.
  unfold genFlows; intros.
  eapply HT_strengthen_premise.
  eapply subset_arrays_spec_wp; eauto. 
  go_match.
  destruct H as [l [l' [z [z' [s0 Hint]]]]]. intuition.
  substs. unfold labToZ in *.
  destruct H1 as [zl Hint].
  destruct H0 as [zl' Hint'].
  intuition.
  do 6 eexists; intuition; eauto. 
  specialize (Zsetincl_Z_list_subset l l' zl zl').
  intros Hspec. 
  replace (boolToZ (Z_list_subset_b zl zl')) with (boolToZ (Zset.incl l l')).
  eauto.
  f_equal; erewrite Zsetincl_Z_list_subset; eauto.
Qed.
  

Definition joinPbody :=      (* a p *)
     [Unpack]                (* at ax p *)
  ++ [Swap 2]                (* p ax at *)
  ++ [Unpack]                (* pt px ax at *)   
  ++ [Swap 1]                (* px pt ax at *)
  ++ [Swap 3]                (* at pt ax px *)
  ++ concat_arrays           (* apt ax px *)
  ++ [Swap 1]                (* ax apt px *)
  ++ [Swap 2]                (* px apt ax *)
  ++ [Swap 1]                (* apt px ax *)
  ++ extend_array            (* at' ax *)
  ++ [Pack]                  (* a' *)
.

Section with_hints.


Hint Resolve extends_refl. 
Hint Resolve extends_trans.
Hint Resolve extends_valid_address.

Ltac build_vc wptac :=
  let awp := (try apply_wp; try wptac) in 
  try (eapply HT_compose_flip; [(build_vc wptac; awp)| (awp; eapply HT_strengthen_premise; awp)]).

Lemma joinPbody_spec_wp : forall (Q : memory -> stack -> Prop),
  HT SysTable
   joinPbody
   (fun m s => exists b t vs x xt vs' s0,
                 s = (b,t):::(x,xt):::s0 /\
                 memarr m t vs /\
                 memarr m xt vs' /\
                 (forall r m1,
                    extends m m1 ->
                    ~ valid_address r m ->
                    memarr m1 r ((vs'++vs)++[x]) ->
                    Q m1 ((b,r):::s0)))
   Q.
Proof.
  intros. unfold joinPbody.

  build_vc ltac:(try apply concat_arrays_spec_wp; try apply extend_array_spec_wp; 
                 try apply unpack_spec_wp; try apply pack_spec_wp). 
  split_vc.
  eapply H2; eauto. 
Qed.

End with_hints. 

Definition joinPcode := 
     joinPbody ++ [VRet]
.

Lemma joinPcode_spec : forall raddr b t vs x xt vs' s0 m0,
  memarr m0 t vs -> 
  memarr m0 xt vs' ->
  HTEscape SysTable raddr
    joinPcode
    (fun m s => s = (b,t):::(x,xt)::: CRet raddr true false :: s0 /\ m = m0)
    (fun m s => (exists t', s = (b,t'):::s0 /\ memarr m t' ((vs'++vs)++[x]) /\ ~ valid_address t' m0 /\ extends m0 m,
                 Success)).
Proof.
  intros. 
  eapply HTEscape_compose_flip.
  eapply vret_specEscape.
  eapply HT_strengthen_premise.
  eapply joinPbody_spec_wp. 
  split_vc. subst. 
  split.  eauto.
  split_vc. 
  split. econstructor. 
  split. eauto.
  split_vc. 
Qed.

Lemma joinPcode_spec' : forall raddr b t l x xt l' s0 m0
  (Hm0: mem_def_on_cache m0),
  labToZ l t m0 ->                          
  labToZ l' xt m0 -> 
  HTEscape SysTable raddr
    joinPcode
    (fun m s => s = (b,t):::(x,xt)::: CRet raddr true false :: s0 /\ m = m0)
    (fun m s => (exists t', s = (b,t'):::s0 /\ labToZ (Zset.add x (Zset.union l l')) t' m /\ extends m0 m,
                 Success)).
Proof.
  intros. 
  unfold labToZ in H, H0. 
  destruct H as [c1 [P1 [P2 P3]]].
  destruct H0 as [c2 [Q1 [Q2 Q3]]].
  eapply HTEscape_strengthen_premise.
  eapply HTEscape_weaken_conclusion.
  eapply joinPcode_spec. 
  eapply P1. 
  eapply Q1.
  simpl.  instantiate (1:= x). intros. destruct H as [t' [? [? ?]]]. eexists; intuition eauto.
  unfold labToZ. eexists. split; eauto. split; eauto. intros. 
  rewrite Zset.In_add. rewrite Zset.In_union.
  rewrite in_app_iff. rewrite in_app_iff. rewrite P2. rewrite Q2. 
  intuition. inv H6. intuition. inv H5. subst. right. intuition. 
  intro. destruct (Z_gt_dec t' 6). auto. exfalso. apply H2.  
  eapply mem_def_on_cache_valid_address; eauto. inv H0. apply index_list_Z_valid in H6. omega. 
  eauto.
  eauto.
Qed.

End syscall.

Definition SOPSysTable (fh: list Instr) (id:ident) : option syscall_info :=
  match id with
    | 0%nat => Some (Build_syscall_info _
                       2%nat 
                       (fun s:list (@Atom Zset.t) =>
                          match s with
                            | (v,l2) :: (i,l1) :: nil =>
                              Some (v,Zset.add i (Zset.union l1 l2))
                            | _ => None
                          end)
                       (Z.of_nat (length fh))
                       joinPcode
                    )
    | _ => None
  end.


Global Instance SOPwf (fh: list Instr) : WfConcreteLattice Zset.t ZsetLat SOPClatt (SOPSysTable fh):=
{ labToZ_cache := labToZ_cache_SOP
; labToZ_ZToLab_id := labToZ_ZToLab_id_SOP
; labToZ_inj := labToZ_inj_SOP
; labToZ_extension_comp := labToZ_extension_comp_SOP
; genBot_spec := genBot_spec_SOP (SOPSysTable fh)
; genJoin_spec := genJoin_spec_SOP (SOPSysTable fh)
; genFlows_spec := genFlows_spec_SOP (SOPSysTable fh)
}.

End SOP.
