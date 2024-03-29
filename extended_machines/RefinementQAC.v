Require Import Coq.Strings.String.
Require Import EquivDec.
Require Import List.
Require Import ZArith.
Require Import Lia.

Require Import Utils.
Require Import Lattices.
Require Import CLattices.

(* For labsToZs, should be possible to factor that into another file *)
Require Import FaultRoutine.

Require Import Semantics.
Require Import Instr.
Require Import AbstractCommon.
Require Import Rules.
Require Import Memory.
Require Import QuasiAbstractMachine.
Require Import Concrete.
Require Import ConcreteExecutions.
Require Import ConcreteMachine.
Require Import Determinism.
Require Import Refinement.

Open Scope list_scope.

Set Implicit Arguments.


Section StateRefinement.

Variable cblock : FaultRoutine.block.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.
Variable ctable : CSysTable.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}
        {WFCLatt: WfConcreteLattice cblock ctable T Latt CLatt}.

Definition match_tags l t m := labToVal l t m.
Hint Unfold match_tags : core.

Definition valid_update (m2 m2' : CodeTriples.memory) :=
  mem_eq_except_cache cblock m2 m2'.
Hint Unfold valid_update : core.

Lemma valid_update_match_tags :
  forall t1 t2 m2 m2',
    match_tags t1 t2 m2 ->
    valid_update m2 m2' ->
    match_tags t1 t2 m2'.
Proof. eapply labToVal_cache; eauto. Qed.
Hint Resolve valid_update_match_tags : core.
Hint Resolve labToVal_cache : core.

Notation meminj := (meminj unit privilege).
Notation Meminj := (Meminj T (val privilege) unit privilege match_tags).
Notation match_atoms := (match_atoms T (val privilege) unit privilege match_tags).
Notation match_vals := (match_vals unit privilege).
Notation match_ptrs := (match_ptrs unit privilege).
Notation update_meminj := (update_meminj unit privilege).

Hint Resolve match_vals_eq : core.
Hint Constructors Memory.match_atoms : core.
Hint Constructors Memory.match_vals : core.
Hint Constructors Memory.match_ptrs : core.
Hint Resolve update_meminj_eq : core.
Hint Unfold match_frames : core.

Record Userinj (mi : meminj) : Prop := {

  ui_no_kernel : forall b2, Mem.stamp b2 = Kernel ->
                            mi b2 = None

}.

Lemma userinj_alloc : forall mi z m1 a1 b1 m1' m2 a2 b2 m2',
                      forall (MINJ : Meminj m1' m2' (update_meminj mi b2 b1))
                             (UINJ : Userinj mi)
                             (ALLOC1 : qa_alloc z a1 m1 = Some (b1, m1'))
                             (ALLOC2 : c_alloc User z a2 m2 = Some (b2, m2'))
                             (ATOMS : match_atoms mi a1 a2 m2),
                        Userinj (update_meminj mi b2 b1).
Proof.
  intros.
  constructor.
  intros b2' Hb2'.
  rewrite update_meminj_neq.
  - apply ui_no_kernel; eauto.
  - unfold c_alloc, alloc in ALLOC2.
    destruct (zreplicate z a2); try congruence.
    inv ALLOC2.
    eapply Mem.alloc_stamp in H0.
    congruence.
Qed.

Inductive match_stk_elmt (mi : meminj) : StkElmt T unit -> CStkElmt -> CodeTriples.memory-> Prop :=
| mse_data : forall a1 a2 m2
                    (ATOMS : match_atoms mi a1 a2 m2),
               match_stk_elmt mi (AData a1) (CData a2) m2
| mse_ret : forall pcv pcl pct b m2
                   (TAG : labToVal pcl pct m2),
              match_stk_elmt mi (ARet (pcv,pcl) b) (CRet (pcv,pct) b false) m2.
Hint Constructors match_stk_elmt : core.

Definition match_stacks (mi : meminj) : list (StkElmt T unit) -> list CStkElmt -> CodeTriples.memory -> Prop :=
  fun s1 s2 m2 => Forall2 (fun se1 se2 => match_stk_elmt mi se1 se2 m2) s1 s2.
Hint Unfold match_stacks : core.

Variable fetch_rule :
  forall opcode : OpCode, AllowModify (labelCount opcode).
Variable faultHandler : list Instr.
Hypothesis handler_correct_succeed :
  handler_spec_succeed cblock ctable _ fetch_rule faultHandler.
Hypothesis handler_correct_fail :
  handler_spec_fail cblock ctable _ fetch_rule faultHandler.

Inductive cache_up2date mem : Prop :=
| cu2d_intro :
    forall (DEF : mem_def_on_cache cblock mem)
           (UP2DATE : forall opcode tags pct,
                        cache_hit_mem cblock mem (opCodeToZ opcode) tags pct ->
                        exists vls pcl rpcl rpct rl rt,
                          labsToVals vls mem tags /\
                          labToVal pcl pct mem /\
                          apply_rule (fetch_rule opcode) pcl vls = Some (rpcl, rl) /\
                          labToVal rpcl rpct mem /\ labToVal rl rt mem /\
                          cache_hit_read_mem cblock mem rt rpct),
      cache_up2date mem.

Inductive match_states kc : @qa_state T -> CS -> Prop :=
| qac_intro : forall mi m1 m2 p stk1 stk2 pcv pcl pct
                     (CODE : CodeTriples.code_at 0 kc faultHandler)
                     (MINJ : Meminj m1 m2 mi)
                     (UINJ : Userinj mi)
                     (STK : match_stacks mi stk1 stk2 m2)
                     (CACHE : cache_up2date m2)
                     (PC : labToVal pcl pct m2),
                match_states kc
                             (AState m1 p stk1 (pcv,pcl))
                             (CState m2 kc p stk2 (pcv,pct) false).
Hint Constructors match_states : core.

Lemma alloc_match_stacks :
  forall size
         a1 m1 b1 m1'
         a2 m2 b2 m2'
         mi stk1 stk2
         (STK : match_stacks mi stk1 stk2 m2)
         (ALLOC1 : qa_alloc size a1 m1 = Some (b1, m1'))
         (ALLOC2 : c_alloc User size a2 m2 = Some (b2, m2'))
         (INJ : Meminj m1 m2 mi)
         (DEF : mem_def_on_cache cblock m2),
    match_stacks (update_meminj mi b2 b1) stk1 stk2 m2'.
Proof.
  intros.
  induction STK; constructor; trivial.
  assert (VALID : valid_update m2 m2').
  { constructor; eauto.
    unfold kernel_memory_extension.
    unfold c_alloc, alloc in ALLOC2.
    destruct (zreplicate size a2) as [fr'|]; try congruence.
    inv ALLOC2.
    intros b fr KERNEL NEQ.
    eapply alloc_get_frame_old; eauto. }
  inv H; constructor.
  - inv ATOMS. constructor; eauto.
    inv VALS; try inv PTRS; constructor; constructor; trivial.
    rewrite update_meminj_neq; eauto.
    eapply mi_valid in BLOCK; eauto.
    destruct BLOCK as [? [? [? [? ?]]]].
    unfold c_alloc, alloc in ALLOC2.
    destruct (zreplicate size a2); inv ALLOC2.
    eapply Mem.alloc_get_fresh in H3; eauto.
    congruence.
  - eapply labToVal_cache; eauto.
Qed.

Lemma match_stacks_app :
  forall mi stk1 args2 stk2' m2
         (STKS : match_stacks mi stk1 (args2 ++ stk2') m2),
    exists args1 stk1',
      stk1 = args1 ++ stk1' /\
      match_stacks mi args1 args2 m2 /\
      match_stacks mi stk1' stk2' m2.
Proof.
  intros.
  gdep stk1.
  induction args2 as [|arg args2 IH]; intros stk1 STKS.
  - exists nil. exists stk1. eauto.
  - simpl in STKS.
    inv STKS.
    exploit IH; eauto.
    intros [? [? [? [? ?]]]]. subst.
    repeat eexists; eauto.
    trivial.
Qed.

Lemma match_stacks_length :
  forall mi stk1 stk2 m2
         (STKS : match_stacks mi stk1 stk2 m2),
    length stk1 = length stk2.
Proof. induction 1; simpl; eauto. Qed.
Hint Resolve match_stacks_length : core.

Lemma match_stacks_all_data :
  forall mi stk1 stk2 m2
         (STKS : match_stacks mi stk1 stk2 m2)
         (DATA : forall se2, In se2 stk2 -> exists a2, se2 = CData a2),
    forall se1, In se1 stk1 -> exists a1, se1 = AData a1.
Proof.
  induction 1 as [|se1 se2 stk1 stk2 STKELMT STKS IHSTKS]; intros; inv H.
  - inv STKELMT; eauto.
    specialize (DATA _ (or_introl eq_refl)).
    destruct DATA; simpl; eauto.
    congruence.
  - apply IHSTKS; simpl in *; auto.
Qed.
Hint Resolve match_stacks_all_data : core.

Lemma match_stacks_app_2 :
  forall mi stk11 stk12 stk21 stk22 m2
         (STKS1 : match_stacks mi stk11 stk21 m2)
         (STKS2 : match_stacks mi stk12 stk22 m2),
    match_stacks mi (stk11 ++ stk12) (stk21 ++ stk22) m2.
Proof. intros. eauto using Forall2_app. Qed.
Hint Resolve match_stacks_app_2 : core.

Hint Constructors pop_to_return : core.

Lemma match_stacks_pop_to_return :
  forall mi stk1 stk2 stk2' m2 pcv cpcl b p
         (STKS : match_stacks mi stk1 stk2 m2)
         (POP : c_pop_to_return stk2 (CRet (pcv, cpcl) b p :: stk2')),
    exists pcl stk1',
      labToVal pcl cpcl m2 /\
      pop_to_return stk1 (ARet (pcv, pcl) b :: stk1') /\
      match_stacks mi stk1' stk2' m2.
Proof.
  intros.
  gdep stk2.
  induction stk1 as [|se1 stk1 IH]; intros;
  inv POP; inv STKS;
  match goal with
    | H : match_stk_elmt _ _ _ _ |- _ =>
      inv H; eauto
  end.
  exploit IH; eauto.
  intros [? [? [? [? ?]]]]; subst.
  eauto 7.
Qed.

Lemma match_stacks_index_list :
  forall mi n s1 s2 x2 m2
         (IDX : index_list n s2 = Some x2)
         (STKS : match_stacks mi s1 s2 m2),
    exists x1,
      index_list n s1 = Some x1 /\
      match_stk_elmt mi x1 x2 m2.
Proof.
  induction n as [|n IH]; intros; inv STKS; simpl in *; allinv; eauto.
Qed.

Lemma match_stacks_update_list :
  forall mi n se1 s1 se2 s2 s2' m2
         (STKS : match_stacks mi s1 s2 m2)
         (STKELMTS : match_stk_elmt mi se1 se2 m2)
         (UPD : update_list n se2 s2 = Some s2'),
    exists s1',
      update_list n se1 s1 = Some s1' /\
      match_stacks mi s1' s2' m2.
Proof.
  intros mi n.
  induction n as [|n IH]; intros; inv STKS; simpl in *; try congruence;
  allinv; eauto.
  match goal with
    | H : (match ?UP with _ => _ end) = Some _ |- _ =>
      destruct UP as [s2''|] eqn:?; try congruence
  end.
  allinv.
  exploit (@IH se1); eauto.
  intros [s1'' [EQ ?]].
  rewrite EQ.
  eauto.
Qed.

Lemma match_stacks_swap :
  forall mi n s1 s2 s2' m2
         (SWAP : swap n s2 = Some s2')
         (STKS : match_stacks mi s1 s2 m2),
    exists s1',
      swap n s1 = Some s1' /\
      match_stacks mi s1' s2' m2.
Proof.
  unfold swap.
  intros.
  destruct s2 as [|se2 s2]; try congruence.
  destruct (index_list n (se2 :: s2)) as [se2'|] eqn:IDX2; try congruence.
  exploit match_stacks_index_list; eauto.
  intros [se1' [IDX1 STKELMTS]].
  inversion STKS as [|se1 ?]; subst.
  rewrite IDX1.
  eapply match_stacks_update_list; eauto.
Qed.

Definition pcatom_labToVal (a1:PcAtom T) (a2:PcAtom (val privilege)) m2 :=
  fst a1 = fst a2 /\
  labToVal (snd a1) (snd a2) m2.

Definition pcatom_valToLab (a:PcAtom (val privilege)) m2 : (PcAtom T) :=
  let (v,l) := a in (v,valToLab l m2).

Lemma pcatom_valToLab_labToVal_id :
  forall a1 a2 m2,
    pcatom_labToVal a1 a2 m2 ->
    pcatom_valToLab a2 m2 = a1.
Proof.
  intros.
  unfold pcatom_labToVal, pcatom_valToLab in *.
  destruct a1, a2. simpl in *.
  f_equal; intuition; try congruence.
  eapply labToVal_valToLab_id; eauto.
Qed.

Lemma opCodeToZ_inj: forall o1 o2, opCodeToZ o1 = opCodeToZ o2 -> o1 = o2.
Proof.
  intros o1 o2 Heq.
  destruct o1, o2; inv Heq; try congruence.
Qed.

Open Scope nat_scope.

Lemma labsToVals_cons_hd: forall n a v b v' tags m2,
  S n <= 3 ->
  labsToVals (Vector.cons T a n v) m2 tags ->
  labsToVals (Vector.cons T b n v') m2 tags ->
  a = b.
Proof.
  intros.
  unfold labsToVals in *.
  destruct tags as [[t1 t2] t3].
  unfold nth_labToVal in *.
  destruct (le_lt_dec (S n) 0). inv l.
  intuition.
  unfold Vector.nth_order in H0, H2.
  simpl in H0, H2.
  eapply labToVal_inj with (cblock := cblock) (L := Latt) in H2; eauto.
Qed.

Lemma nth_labToVal_cons:
  forall nth n a v m ts,
    nth_labToVal (Vector.cons T a n v) (S nth) m ts ->
    nth_labToVal v nth m ts.
Proof.
  induction n; simpl; intros.
  - unfold nth_labToVal in *.
    case_eq (le_lt_dec (S nth) 1); case_eq (le_lt_dec nth 0); intros; auto;
    try (zify ; lia).
  - unfold nth_labToVal in *.
    destruct (le_lt_dec (S (S n)) (S nth)) eqn:E; case_eq (le_lt_dec (S n) nth); intros; auto;
    try (zify ; lia).
    unfold Vector.nth_order in *. simpl in H.
    erewrite of_nat_lt_proof_irrel ; eauto.
Qed.

Lemma labsToVals_cons_tail:
  forall n0 a v0 b v3 ts m,
    (n0 <= 2)%nat ->
    labsToVals (Vector.cons T a n0 v0) m ts ->
    labsToVals (Vector.cons T b n0 v3) m ts ->
    exists ts',
      labsToVals v0 m ts' /\  labsToVals v3 m ts'.
Proof.
  intros.
   unfold labsToVals in *.
  destruct ts as ((z0 & z1) & z2).
  destruct H0 as (T1 & T2 & T3).
  destruct H1 as (U1 & U2 & U3).
  exists (z1,z2,dontCare); repeat split;
  try (eapply nth_labToVal_cons; eauto; fail).
  unfold nth_labToVal.
  destruct (le_lt_dec n0 2); auto; zify ; lia.
  unfold nth_labToVal.
  destruct (le_lt_dec n0 2); auto; zify ; lia.
Qed.

Lemma labsToVals_inj: forall n (v1 v2: Vector.t T n), n <= 3 ->
     forall ts m,
     labsToVals v1 m ts -> labsToVals v2 m ts -> v1 = v2.
Proof.
  intros n v1 v2.
  set (P:= fun n (v1 v2: Vector.t T n) => n <= 3 -> forall ts m,
                                                 labsToVals v1 m ts -> labsToVals v2 m ts -> v1 = v2) in *.
  apply Vector.rect2 with (P0:=P); unfold P; eauto.
  intros n0 v0 v3 H a b H0 ts m H1 H2.
  assert (a=b) by (eapply labsToVals_cons_hd; eauto).
  subst.
  f_equal.
  elim labsToVals_cons_tail with (2:=H1) (3:=H2).
  intros ts' (T1 & T2).
  apply H with ts' m; auto.
  zify; lia.
  zify; lia.
Qed.

Inductive match_events : Event T -> CEvent -> Prop :=
  | me_intro : forall e1 e2 m
                      (ATOMS : pcatom_labToVal e1 e2 m),
                 match_events (EInt e1) (CEInt e2 m).

Variable atable : ASysTable T.

Let match_actions e1 e2 := match_actions match_events e1 e2.

Lemma cache_hit_read_mem_extends :
  forall m m' rpct rt
         (EXT : extends m m')
         (HIT : cache_hit_read_mem cblock m rpct rt),
    cache_hit_read_mem cblock m' rpct rt.
Proof.
  intros.
  unfold cache_hit_read_mem in *.
  destruct (Mem.get_frame m cblock) as [fr|] eqn:FRAME; try solve [inversion HIT].
  apply EXT in FRAME.
  rewrite FRAME.
  assumption.
Qed.

Lemma cache_hit_mem_extends_inv :
  forall m m' op tags pct
         (DEF : mem_def_on_cache cblock m)
         (EXT : extends m m')
         (HIT : cache_hit_mem cblock m' op tags pct),
    cache_hit_mem cblock m op tags pct.
Proof.
  intros.
  unfold cache_hit_mem in *.
  destruct DEF as [fr FRAME]. rewrite FRAME.
  eapply EXT in FRAME.
  rewrite FRAME in HIT.
  assumption.
Qed.

Lemma mem_alloc_extends :
  forall {T S} (eqS : EqDec S eq) (m m' : memory T S) mode p fr b
         (ALLOC : Mem.alloc mode m p fr = (b, m')),
    extends m m'.
Proof.
  intros.
  intros b' fr' DEF.
  eapply alloc_get_frame_old; eauto.
Qed.

Lemma cache_up2date_alloc : forall p size m a b m'
                                   (ALLOC : c_alloc p size a m = Some (b, m'))
                                   (CACHE : cache_up2date m),
                              cache_up2date m'.
Proof.
  unfold c_alloc, alloc.
  intros.
  destruct (zreplicate size a); try congruence.
  inv ALLOC.
  destruct CACHE.
  econstructor; eauto.
  - unfold mem_def_on_cache in *.
    destruct DEF.
    erewrite alloc_get_frame_old; eauto.
  - intros opcode tags pct HIT'.
    specialize (UP2DATE opcode tags pct).
    destruct UP2DATE as (vls & pcl & rpcl & rpct & rl & rt & H1 & H2 & H3 & H4 & H5 & H6);
      eauto using mem_alloc_extends, cache_hit_mem_extends_inv.
    exists vls, pcl, rpcl, rpct, rl, rt.
    assert (EXT : extends m m').
    { unfold extends. intros. eapply alloc_get_frame_old; eauto. }
    repeat split;
    eauto using labToVal_extension_comp, cache_hit_read_mem_extends,
                labsToVals_extension_comp.
Qed.

Lemma store_cache_up2date :
  forall p a m m'
         (STORE : store p a m = Some m')
         (STAMP : Mem.stamp (fst p) = User)
         (CACHE : cache_up2date m),
    cache_up2date m'.
Proof.
  intros. destruct p as [b off]. simpl in *.
  destruct CACHE.
  constructor.
  - unfold store in STORE. simpl in *.
    destruct (Mem.get_frame m b) as [fr|] eqn:FRAME; try solve [inversion STORE].
    destruct (upd_m off a fr) as [fr'|] eqn:FRAME'; try solve [inversion STORE].
    unfold mem_def_on_cache in *. destruct DEF as [fr'' DEF].
    erewrite get_frame_upd_frame_neq; eauto. congruence.
  - intros opcode tags pct HIT'.
    assert (HIT : cache_hit_mem cblock m (opCodeToZ opcode) tags pct).
    { unfold cache_hit_mem in *.
      destruct (Mem.get_frame m' cblock) as [cache|] eqn:CACHE'; try solve [inversion HIT'].
      erewrite get_frame_store_neq in CACHE'; eauto; try congruence.
      rewrite CACHE'.
      assumption. }
    assert (EQ : mem_eq_except_cache cblock m m').
    { constructor; trivial.
      intros b' fr' KERNEL NEQ FRAME.
      erewrite get_frame_store_neq; eauto.
      congruence. }
    specialize (UP2DATE _ _ _ HIT).
    destruct UP2DATE as (vls & pcl & rpcl & rpct & rl & rt & ? & ? & ? & ? & ? & READ').
    repeat eexists; eauto using labsToVals_cache.
    clear - STORE READ' stamp_cblock STAMP.
    unfold cache_hit_read_mem in *.
    destruct (Mem.get_frame m cblock) as [cache|] eqn:CACHE; try solve [inversion READ'].
    erewrite <- get_frame_store_neq in CACHE;
    eauto using labsToVals_extension_comp; try congruence.
    rewrite CACHE.
    assumption.
Qed.

Lemma alloc_stamp :
  forall T S (eqS : EqDec S eq) mode (stamp : S) size (a : Atom T S) mem b mem'
         (ALLOC: alloc mode stamp size a mem = Some (b, mem')),
    Mem.stamp b = stamp.
Proof.
  unfold alloc.
  intros.
  destruct (zreplicate size a) eqn:?; try congruence.
  inv ALLOC.
  eapply Mem.alloc_stamp; eauto.
Qed.
Hint Resolve alloc_stamp : core.

Lemma cache_up2date_res :
  forall tmuc opcode vls ts pcl pct
         (UP2DATE : cache_up2date tmuc)
         (Hvls : labsToVals vls tmuc ts)
         (Hpc : labToVal pcl pct tmuc)
         (HIT : cache_hit_mem cblock tmuc (opCodeToZ opcode) ts pct),
    exists rpcl rpct rl rt,
      labToVal rpcl rpct tmuc /\
      labToVal rl rt tmuc /\
      apply_rule (fetch_rule opcode) pcl vls = Some (rpcl, rl) /\
      cache_hit_read_mem cblock tmuc rt rpct.
Proof.
  intros.
  destruct UP2DATE.
  eapply UP2DATE in HIT; eauto.
  destruct HIT as (vls' & pcl' & rpcl & rpct & rl & rt & H1 & H2 & H3 & H4 & H5 & H6).
  assert (vls' = vls).
  { eapply labsToVals_inj; eauto.
    apply labelCountBounds. }
  subst vls'.
  assert (pcl' = pcl) by (eapply labToVal_inj; eauto). subst pcl'.
  eexists rpcl, rpct, rl, rt. eauto.
Qed.

Lemma analyze_cache_hit :
  forall m opcode (vls : Vector.t T (labelCount opcode)) ts pcl pct zrl zrpcl
         (LABS : labsToVals vls m ts)
         (PC : labToVal pcl pct m)
         (UP2DATE : cache_up2date m)
         (CHIT : cache_hit_mem cblock m (opCodeToZ opcode) ts pct)
         (CREAD : cache_hit_read_mem cblock m zrl zrpcl),
  exists rpcl rl,
    labToVal rl zrl m /\
    labToVal rpcl zrpcl m /\
    apply_rule (fetch_rule opcode) pcl vls = Some (rpcl, rl).
Proof.
  intros.
  exploit cache_up2date_res; eauto.
  intros (rpcl & rpct & rl & rt & H1 & H2 & H3 & H4).
  generalize (cache_hit_read_mem_determ cblock m _ _ _ _ CREAD H4).
  intuition (subst; eauto).
Qed.

Ltac get_opcode :=
  match goal with
    | INST : read_m _ _ = Some ?instr |- _ =>
      let opcode := (eval compute in (opcode_of_instr instr)) in
      match opcode with
        | Some ?opcode => opcode
      end
  end.

Ltac abstract_tag tag :=
  match goal with
    | H : labToVal ?l tag _ |- _ => l
    | H : match_tags ?l tag _ |- _ => l
  end.

Ltac quasi_abstract_labels opcode :=
  match goal with
    | H : context[cache_hit_mem _ _ _ ?tags _] |- _ =>
      match tags with
        | (dontCare, dontCare, dontCare) =>
          constr:(<||> : Vector.t T (labelCount opcode))
        | (?t1, dontCare, dontCare) =>
          let l1 := abstract_tag t1 in
          constr:(<|l1|> : Vector.t T (labelCount opcode))
        | (?t1, ?t2, dontCare) =>
          let l1 := abstract_tag t1 in
          let l2 := abstract_tag t2 in
          constr:(<|l1; l2|> : Vector.t T (labelCount opcode))
        | (?t1, ?t2, ?t3) =>
          let l1 := abstract_tag t1 in
          let l2 := abstract_tag t2 in
          let l3 := abstract_tag t3 in
          constr:(<|l1; l2; l3|> : Vector.t T (labelCount opcode))
      end
    | |- _ => fail 1 "quasi_abstract_labels" opcode
  end.

Ltac analyze_cache_hit :=
  (* Find the current opcode, build the label vector use cache_up2date
  to build an equation about apply_rule. *)
  let opcode := get_opcode in
  match goal with
    | CACHE : cache_up2date _,
      CHIT : cache_hit_mem cblock ?tmuc _ ?tags ?pct,
      CREAD : cache_hit_read_mem cblock _ _ _ |- _ =>
      let vls := quasi_abstract_labels opcode in
      let pcl := abstract_tag pct in
      exploit (@analyze_cache_hit tmuc opcode vls tags pcl pct);
      unfold labsToVals, nth_labToVal; simpl; eauto;
      let rpcl := fresh "rpcl'" in
      let rl := fresh "rl'" in
      intros [rpcl [rl [? [? ?]]]]; subst
    | |- _ => fail 1 "Failed in case" opcode
  end.

Ltac match_inv :=
  (* Invert some hypotheses *)
  unfold match_stacks in *;
  repeat match goal with
           | H : ?x = ?x |- _ => clear H
           | H : Forall2 _ _ (_ ::: _) |- _ => inv H
           | H : Forall2 _ _ (_ ++ _) |- _ =>
             exploit Forall2_app_inv_r; eauto;
             intros [? [? [? [? ?]]]];
             clear H
           | H : match_stk_elmt _ _ (CData _) _ |- _ => inv H
         end;
  repeat match goal with
           | H : match_atoms _ _ (?v, _) _ |- _ =>
             match goal with
               | H : match_vals _ _ v |- _ => fail 1
               | |- _ => inversion H; subst
             end
         end;
  repeat match goal with
           | H : match_vals _ _ (Vint _) |- _ => inv H
           | H : match_vals _ _ (Vptr _) |- _ => inv H
           | H : match_ptrs _ _ _ |- _ => inv H
           | H : match_tags ?l ?t _ |- _ =>
             unfold match_tags in H; subst t
         end.

Ltac on_case test message t :=
  match goal with
    | |- _ => test; (t || fail 1 message)
    | |- _ => idtac
  end.

Ltac instr opcode :=
  idtac;
  let opcode' := get_opcode in
  match opcode' with
    | opcode => idtac
  end.

Ltac complete_exploit lemma :=
  exploit lemma;
  eauto;
  [intros H;
   repeat match goal with
            | H : exists _, _ |- _ => destruct H
            | H : _ /\ _ |- _ => destruct H
          end;
   subst].

Lemma match_vals_eq :
  forall m1 m2 mi v11 v12 v21 v22
         (INJ : Meminj m1 m2 mi)
         (VALS1 : match_vals mi v11 v21)
         (VALS2 : match_vals mi v12 v22),
    match_vals mi (val_eq v11 v12)
                  (val_eq v21 v22).
Proof.
  intros. unfold val_eq.
  destruct (v11 == v12) as [E1 | E1]; compute in E1; subst;
  destruct (v21 == v22) as [E2 | E2]; compute in E2; subst;
  auto;
  repeat match goal with
           | H : match_vals _ _ _ |- _ => inv H
           | H : match_ptrs _ _ _ |- _ => inv H
         end; try congruence.
  cut (b2 = b3); try congruence.
  eapply mi_inj; eauto.
Qed.
Hint Resolve match_vals_eq : core.

Lemma cache_hit_mem_mem_def_on_cache :
  forall m o ts pct
         (HIT : cache_hit_mem cblock m o ts pct),
    mem_def_on_cache cblock m.
Proof.
  intros.
  unfold cache_hit_mem in HIT.
  destruct (Mem.get_frame m cblock) as [cache|] eqn:FRAME; intuition.
  eexists; eauto.
Qed.
Hint Resolve cache_hit_mem_mem_def_on_cache : core.

Lemma cache_hit_read_mem_mem_def_on_cache :
  forall m rpct rt
         (HIT : cache_hit_read_mem cblock m rpct rt),
    mem_def_on_cache cblock m.
Proof.
  intros.
  unfold cache_hit_read_mem in HIT.
  destruct (Mem.get_frame m cblock) as [cache|] eqn:FRAME; intuition.
  eexists; eauto.
Qed.
Hint Resolve cache_hit_read_mem_mem_def_on_cache : core.

Lemma store_user_valid_update :
  forall p a m2 m2'
         (DEF : mem_def_on_cache cblock m2)
         (STORE : store p a m2 = Some m2')
         (USER : Mem.stamp (fst p) = User),
    valid_update m2 m2'.
Proof.
  intros. destruct p as [b off]. simpl in *.
  constructor; eauto.
  intros b' fr KERNEL NEQ H.
  rewrite <- H.
  eapply get_frame_store_neq; eauto.
  congruence.
Qed.
Hint Resolve store_user_valid_update : core.


Lemma alloc_user_valid_update :
  forall size a m b m'
         (DEF : mem_def_on_cache cblock m)
         (ALLOC : c_alloc User size a m = Some (b, m')),
    valid_update m m'.
Proof.
  intros.
  constructor; eauto.
  intros b' fr KERNEL NEQ FRAME.
  unfold c_alloc, alloc in ALLOC.
  destruct (zreplicate size a) as [fr'|]; inv ALLOC.
  rewrite <- FRAME.
  eapply alloc_get_frame_neq; eauto.
  cut (Mem.stamp b = User); try congruence.
  eapply Mem.alloc_stamp; eauto.
Qed.
Hint Resolve alloc_user_valid_update : core.

Lemma match_atoms_valid_update :
  forall mi a1 a2 m2 m2'
         (VALID : valid_update m2 m2')
         (ATOMS : match_atoms mi a1 a2 m2),
    match_atoms mi a1 a2 m2'.
Proof. intros. inv ATOMS. eauto. Qed.
Hint Resolve match_atoms_valid_update : valid_update.

Lemma match_stk_elmt_valid_update :
  forall mi se1 se2 m2 m2'
         (VALID : valid_update m2 m2')
         (STKELMTS : match_stk_elmt mi se1 se2 m2),
    match_stk_elmt mi se1 se2 m2'.
Proof. intros. inv STKELMTS; eauto with valid_update. Qed.
Hint Resolve match_stk_elmt_valid_update : valid_update.

Lemma match_stacks_valid_update :
  forall mi stk1 stk2 m2 m2'
         (VALID : valid_update m2 m2')
         (STKS : match_stacks mi stk1 stk2 m2),
    match_stacks mi stk1 stk2 m2'.
Proof. intros. induction STKS; eauto with valid_update. Qed.
Hint Resolve match_stacks_valid_update : valid_update.

(** Cache hit case *)

Lemma cache_hit_simulation :
  forall kc s1 s2 a2 s2'
         (Hmatch : match_states kc s1 s2)
         (Hs2' : priv s2' = false)
         (Hstep : cstep cblock ctable s2 a2 s2'),
    exists a1 s1', step_rules fetch_rule atable s1 a1 s1' /\
                   match_actions a1 a2 /\
                   match_states kc s1' s2'.
Proof.
  intros.
  inv Hmatch.

  inv Hstep; inv CS1; simpl in *; try congruence;

  match_inv; simpl in *;

  on_case ltac:(instr OpAdd)
          "Couldn't analyze Add"
          ltac:(complete_exploit add_defined);

  on_case ltac:(instr OpSub)
          "Couldn't analyze Sub"
          ltac:(complete_exploit (sub_defined unit privilege));

  on_case ltac:(instr OpAlloc)
          "Couldn't analyze Alloc"
          ltac:(idtac;
                match goal with
                  | ALLOC : c_alloc _ _ _ ?m2 = Some (_, ?m2'),
                    CACHE : cache_up2date _ |- _ =>
                    exploit (meminj_alloc T (val privilege) unit privilege _ _ valid_update_match_tags);
                    eauto; try solve [constructor; eauto];
                    intros [? [? [? ?]]];
                    exploit userinj_alloc; eauto; intro;
                    exploit alloc_match_stacks; eauto; intro;
                    generalize (cache_up2date_alloc _ _ _ ALLOC CACHE); intro;
                    assert (valid_update m2 m2') by eauto
                end);

  on_case ltac:(first [instr OpLoad | instr OpStore])
          "Couldn't analyze Load or Store"
          ltac:(exploit meminj_load; eauto using mp_intro;
                intros (? & ? & ?); match_inv);

  on_case ltac:(first [instr OpRet | instr OpVRet])
          "Couldn't analyze Ret cases"
          ltac:(complete_exploit match_stacks_pop_to_return);

  analyze_cache_hit;

  on_case ltac:(instr OpStore)
          "Couldn't construct memory update"
          ltac:(exploit (meminj_store T (val privilege) unit privilege _ _ valid_update_match_tags);
                eauto; try solve [constructor; eauto];
                intros [? [? ?]];
                match goal with
                  | MUPDT : store _ _ ?m2 = Some ?m2',
                    STAMP : Mem.stamp _ = User,
                    CREAD : cache_hit_read_mem _ _ _ _ |- _ =>
                    generalize (@store_cache_up2date _ _ _ _ MUPDT STAMP CACHE); intro;
                    assert (valid_update m2 m2') by eauto
                end);

  on_case ltac:(instr OpCall)
          "Couldn't exploit Call case"
          ltac:(idtac;
                match goal with
                  | MATCH : Forall2 (fun _ _ => match_stk_elmt ?mi _ _ ?mem) ?aargs ?cargs,
                    ARGS : forall se, In se ?cargs -> _ |- _ =>
                    generalize (@match_stacks_all_data mi aargs cargs mem MATCH ARGS); intro
                end);

  on_case ltac:(instr OpBranchNZ)
          "Case analysis for BranchNZ failed"
          ltac:(idtac;
                match goal with
                  | |- context[if (?z =? 0)%Z then _ else _ ] =>
                    let H := fresh "H" in
                    assert (H := Z.eqb_spec z 0);
                    destruct (z =? 0)%Z;
                    inv H
                end);

  on_case ltac:(instr OpSizeOf)
          "Length analysis for SizeOf failed"
          ltac:(exploit mi_valid'; eauto; intros (? & ? & FRAMES);
                apply Forall2_length in FRAMES; rewrite <- FRAMES);

  solve [
      eexists; eexists; split; try split;
      try [> once (econstructor; solve [compute; eauto]) ..];
      repeat (econstructor; eauto); simpl; f_equal; intuition (eauto 7 with valid_update)
    ].

Qed.

Open Scope Z_scope.

Lemma cupd_mem_eq_except_cache :
  forall m2 cache m2'
         (UPD : cupd cblock m2 cache = Some m2'),
    mem_eq_except_cache cblock m2 m2'.
Proof.
  unfold cupd.
  intros.
  constructor.
  - unfold mem_def_on_cache.
    eapply Mem.upd_frame_defined; eauto.
  - intros b' fr KERNEL NEQ EQ.
    rewrite <- EQ.
    eapply get_frame_upd_frame_neq; eauto.
Qed.
Hint Resolve cupd_mem_eq_except_cache : core.

Lemma configuration_at_miss :
  forall kc s1 s21 e2 s22
         (MATCH : match_states kc s1 s21)
         (STEP : cstep cblock ctable s21 e2 s22)
         (NOTSYSCALL : forall id, read_m (fst (pc s21)) (imem s21) <> Some (SysCall id))
         (PRIV : priv s22 = true),
    exists opcode (vls : Vector.t T (labelCount opcode)) ts pct,
      labsToVals vls (mem s22) ts /\
      labToVal (snd (apc s1)) pct (mem s22) /\
      cupd cblock (mem s21)
           (build_cache (opCodeToZ opcode) ts pct) = Some (mem s22) /\
      fhdl s22 = fhdl s21 /\
      imem s22 = imem s21 /\
      stk s22 = CRet (pc s21) false false :: stk s21 /\
      pc s22 = (0, handlerTag).
Proof.
  intros.
  inv MATCH.
  inv STEP; inv CS1; simpl in *; try congruence;

  match_inv;

  on_case ltac:(first [instr OpLoad | instr OpStore])
          "Couldn't analyze Load or Store"
          ltac:(exploit meminj_load; eauto using mp_intro;
                intros (? & ? & ?); match_inv);

  on_case ltac:(first [instr OpRet | instr OpVRet])
          "Couldn't analyze Ret cases"
          ltac:(complete_exploit match_stacks_pop_to_return);

  let opcode := get_opcode in
  let vls := quasi_abstract_labels opcode in
  exists opcode; exists vls;
  match goal with
    | H : context[cache_hit_mem _ _ _ ?ts ?pct] |- _ =>
      exists ts; exists pct
  end;

  solve [
      simpl; repeat econstructor;
      unfold nth_labToVal, Vector.nth_order; simpl; eauto;
      eapply labToVal_cache; eauto
    ].

Qed.

Lemma configuration_at_syscall :
  forall s21 e2 s22 id
         (STEP : cstep cblock ctable s21 e2 s22)
         (SYSCALL : read_m (fst (pc s21)) (imem s21) = Some (SysCall id))
         (PRIV : priv s21 = false),
    exists id entry args s0,
       read_m (fst (pc s21)) (imem s21) = Some (SysCall id) /\
       ctable id = Some {| csi_arity := length args;
                           csi_pc := entry |} /\
       mem s22 = mem s21 /\
       fhdl s22 = fhdl s21 /\
       imem s22 = imem s21 /\
       stk s22 = map CData args ++ CRet (fst (pc s21) + 1, snd (pc s21)) true false :: s0 /\
       stk s21 = map CData args ++ s0 /\
       pc s22 = (entry, handlerTag) /\
       priv s22 = true /\
       e2 = Silent.
Proof.
  intros.
  inv STEP; simpl in *; try congruence.
  match goal with
    | sys_info : CSysCall |- _ =>
      destruct sys_info; simpl in *; subst
  end.
  repeat eexists; eauto.
Qed.

Lemma build_cache_cache_hit :
  forall m2 m2' opcode tags pct
         (UPD : cupd cblock m2 (build_cache opcode tags pct) = Some m2'),
    cache_hit_mem cblock m2' opcode tags pct.
Proof.
  unfold cupd, cache_hit_mem.
  intros.
  erewrite get_frame_upd_frame_eq; eauto.
  apply build_cache_hit.
Qed.

Lemma meminj_same_frames :
  forall mi m1 m2 m2'
         (INJ : Meminj m1 m2 mi)
         (VALID : valid_update m2 m2')
         (EQ : forall b1 b2,
                 mi b2 = Some b1 ->
                 Mem.get_frame m2 b2 = Mem.get_frame m2' b2),
    Meminj m1 m2' mi.
Proof.
  intros.
  constructor.

  - intros.
    exploit EQ; eauto.
    intros E. rewrite <- E.
    exploit mi_valid; eauto.
    intros (f1 & f2 & H1 & H2 & H3).
    repeat eexists; eauto.
    clear - H3 VALID stamp_cblock ctable Latt WFCLatt.
    induction H3; eauto.
    constructor; eauto with valid_update.

  - intros.
    destruct (mi b2) as [b1|] eqn:Hb2; try congruence.
    exploit EQ; eauto.
    exploit mi_valid; eauto.
    intros [? [? [? [? ?]]]].
    congruence.

  - eapply mi_inj; eauto.

Qed.

Lemma build_cache_meminj :
  forall mi m1 m2 m2' cache
         (MINJ : Meminj m1 m2 mi)
         (UINJ : Userinj mi)
         (UPD : cupd cblock m2 cache = Some m2'),
    Meminj m1 m2' mi.
Proof.
  unfold cupd.
  intros.
  eapply meminj_same_frames; eauto.
  intros.
  erewrite <- get_frame_upd_frame_neq; eauto.
  exploit ui_no_kernel; eauto.
  congruence.
Qed.

Lemma invalid_pc_no_step :
  forall s1 e s2
         (STEP : cstep cblock ctable s1 e s2)
         (FAIL : fst (pc s1) < 0),
    False.
Proof.
  intros.
  inv STEP; simpl in *;
  unfold read_m in *;
  generalize (Z.ltb_spec0 pcv 0);
  let H := fresh "H" in
  intros H;
  destruct (pcv <? 0); inv H; intuition; congruence.
Qed.

Lemma kernel_run_success_fail_contra :
  forall s1 s21 s22
         (RUN1 : runsUntilUser cblock ctable s1 s21)
         (RUN2 : runsToEnd cblock ctable s1 s22)
         (FAIL : fst (pc s22) < 0),
    False.
Proof.
  intros.
  induction RUN1; inv RUN2;
  try match goal with
        | [ H1 : cstep _ _ ?s _ _,
            H2 : cstep _ _ ?s _ _
            |- _ ] =>
          let H := fresh "H" in
          generalize (cmach_determ H1 H2);
          intros [? ?]; subst
      end; eauto;
  try match goal with
        | [ H : runsUntilUser _ _ _ _ |- _ ] =>
          generalize (runsUntilUser_l H);
          intros
      end;
  try match goal with
        | [ H : runsToEnd _ _ _ _ |- _ ] =>
          generalize (runsToEnd_l H);
          intros
      end;
  try congruence;
  eauto using invalid_pc_no_step ; eauto.
Qed.

Lemma kernel_fail_determ :
  forall s1 s21 s22
         (RUN1 : runsToEnd cblock ctable s1 s21)
         (FAIL1 : fst (pc s21) < 0)
         (RUN2 : runsToEnd cblock ctable s1 s22)
         (FAIL2 : fst (pc s22) < 0),
    s21 = s22.
Proof.
  intros.
  induction RUN1; inv RUN2; trivial;
  try solve [exfalso; eauto using invalid_pc_no_step];
  try match goal with
        | [ H1 : cstep _ _ ?s _ _,
            H2 : cstep _ _ ?s _ _
            |- _ ] =>
          let H := fresh "H" in
          generalize (cmach_determ H1 H2);
          intros [? ?]; subst
      end; eauto.
Qed.

Lemma runsToEscape_determ :
  forall s1 s21 s22
         (RUN1 : runsToEscape cblock ctable s1 s21)
         (RUN2 : runsToEscape cblock ctable s1 s22),
    s21 = s22.
Proof.
  intros.
  inv RUN1; inv RUN2;
  eauto using runsUntilUser_determ,
              kernel_fail_determ;
  try solve [exfalso; eauto using kernel_run_success_fail_contra];
  try match goal with
        | [ H : runsUntilUser _ _ _ _ |- _ ] =>
          generalize (runsUntilUser_l H);
          intros
      end;
  try match goal with
        | [ H : runsToEnd _ _ _ |- _ ] =>
          generalize (runsToEnd_l H);
          intros
      end;
  try congruence.
Qed.

Lemma handler_final_mem_meminj :
  forall mi m1 m2 m2' rpcl rpct rl rt
         (MINJ : Meminj m1 m2 mi)
         (UINJ : Userinj mi)
         (DEF : mem_def_on_cache cblock m2)
         (MATCH : handler_final_mem_matches cblock rpcl rl m2 m2' rpct rt),
    Meminj m1 m2' mi.
Proof.
  intros.
  destruct MATCH as (m_ext & EXT & PC & RES & HIT & UP).
  destruct UP as [UP CACHE].
  eapply meminj_same_frames; eauto.
  - split; eauto.
    intros b fr KERNEL NEQ FRAME.
    apply EXT in FRAME.
    destruct UP as [_ UP].
    eapply UP; eauto.
  - intros.
    destruct UP as [USER KERNEL].
    exploit mi_valid; eauto.
    intros (f1 & f2 & FRAME1 & FRAME2 & MATCH).
    rewrite FRAME2. symmetry.
    apply USER; eauto.
    destruct (Mem.stamp b2) eqn:STAMP; trivial.
    exploit ui_no_kernel; eauto.
    congruence.
Qed.

Lemma handler_final_mem_matches_labToVal_preserved :
  forall l m m' z rpcl rl zpc zr,
    handler_final_mem_matches cblock rpcl rl m m' zpc zr ->
    labToVal l z m ->
    mem_def_on_cache cblock m ->
    labToVal l z m'.
Proof.
  intros.
  inv H. intuition.
  exploit extends_mem_def_on_cache; eauto. intros Hx.
  unfold update_cache_spec_rvec in H6.
  eapply labToVal_cache; eauto.
  destruct H6.
  constructor; auto.
  intros b.
  destruct H5. eauto.
Qed.

Lemma handler_final_mem_matches_labsToVals_preserved :
  forall m m' n (vls: Vector.t T n) zz rpcl rl zpc zr,
    handler_final_mem_matches cblock rpcl rl m m' zpc zr ->
    labsToVals vls m zz ->
    mem_def_on_cache cblock m ->
    labsToVals vls m' zz .
Proof.
  intros. destruct zz as [[t1 t2] t3]. inv H0. intuition.
  simpl. unfold nth_labToVal in *.
  destruct (le_lt_dec n 0);
  destruct (le_lt_dec n 1);
  destruct (le_lt_dec n 2); subst; intuition; eauto using handler_final_mem_matches_labToVal_preserved.
Qed.

(* This lemma says: if the cache input matches some configuration, and
the handler runs, yielding a new memory, then that memory's cache also
matches the same configuration. *)

Lemma update_cache_spec_rvec_cache_hit :
  forall rpcl rl rpct rt m2 m2' op tags pc
         (MATCH : handler_final_mem_matches cblock rpcl rl m2 m2' rpct rt)
         (HIT : cache_hit_mem cblock m2 op tags pc),
    cache_hit_mem cblock m2' op tags pc.
Proof.
  intros.
  unfold cache_hit_mem in *.
  destruct (Mem.get_frame m2 cblock) as [cache|] eqn:CACHE; try solve [inversion HIT].
  destruct MATCH as (m2'' & EXT & ? & ? & READ & ? & E).
  apply EXT in CACHE.
  unfold load, cache_hit_read_mem in *. simpl in *.
  destruct (Mem.get_frame m2' cblock) as [cache'|] eqn:CACHE'; try solve [inversion READ].
  destruct READ.
  rewrite CACHE in E.
  inv HIT;
  repeat match goal with
           | H : tag_in_mem _ _ _ |- _ =>
             inv H
         end.
  econstructor; econstructor;
  try solve [rewrite <- E; eauto; compute; congruence]; eauto.
Qed.

Lemma cache_hit_unique:
  forall mem opcode opcode' labs labs' pcl pcl',
    forall
      (CHIT: cache_hit_mem cblock mem opcode labs pcl)
      (CHIT': cache_hit_mem cblock mem opcode' labs' pcl'),
      opcode = opcode' /\
      labs = labs' /\
      pcl = pcl'.
Proof.
  intros.
  unfold cache_hit_mem in *.
  destruct (Mem.get_frame mem cblock) as [fr|] eqn:FRAME;
  inv CHIT; inv CHIT'.
  inv OP; inv OP0.
  inv TAG1; inv TAG0.
  inv TAG2; inv TAG4.
  inv TAG3; inv TAG5.
  inv TAGPC; inv TAGPC0.
  repeat allinv'.
  intuition.
Qed.

(* This lemma says: if the rule table says "yes" for some inputs and
we start in kernel mode with a cache with those inputs, then the final
memory has an up-to-date cache w.r.t. those inputs. *)

Lemma handler_final_mem_cache_up2date :
  forall m2 m2' opcode (vls : Vector.t T (labelCount opcode)) ts pcl pct
         rpcl rl zpc zr
         (Hvls : labsToVals vls m2 ts) (Hpc : labToVal pcl pct m2)
         (HIT : cache_hit_mem cblock m2 (opCodeToZ opcode) ts pct)
         (OK : apply_rule (fetch_rule opcode) pcl vls = Some (rpcl, rl))
         (MATCH : handler_final_mem_matches cblock rpcl rl m2 m2' zpc zr),
    cache_up2date m2'.
Proof.
  intros.
  constructor.
  - destruct MATCH as (? & ? & ? & ? & ? & ?); eauto.
  - intros opcode' tags pct' HIT'.
    exploit update_cache_spec_rvec_cache_hit; eauto.
    intros HIT''.
    generalize (cache_hit_unique _ _ _ _ _ _ _ HIT' HIT'').
    intros [E1 [E2 E3]].
    apply opCodeToZ_inj in E1. subst.
    exploit handler_final_mem_matches_labToVal_preserved; eauto. intro.
    exploit handler_final_mem_matches_labsToVals_preserved; eauto. intro.
    exists vls, pcl, rpcl, zpc, rl, zr.
    split; eauto.
    apply cache_hit_mem_mem_def_on_cache in HIT.
    destruct MATCH; intuition eauto.
Qed.
Hint Resolve handler_final_mem_cache_up2date : core.

Lemma cache_miss_simulation :
  forall kc s1 s21 e21 s22 s23
         (MATCH : match_states kc s1 s21)
         (NOTSYSCALL : forall id, read_m (fst (pc s21)) (imem s21) <> Some (SysCall id))
         (STEP1 : cstep cblock ctable s21 e21 s22)
         (RUN : runsUntilUser cblock ctable s22 s23),
    match_states kc s1 s23.
Proof.
  intros.
  exploit runsUntilUser_l; eauto.
  intros PRIV.
  exploit configuration_at_miss; eauto.
  intros (op & vls & [[t1 t2] t3] & pct & Hvls & Hpc & MEM & EQS).
  exploit build_cache_cache_hit; eauto. intros HIT.
  inv MATCH.
  exploit build_cache_meminj; eauto. intros MINJ'.
  destruct s22. simpl in EQS.
  intuition.
  simpl in MEM, MINJ', PRIV.
  subst.
  destruct (apply_rule (fetch_rule op) pcl vls)
    as [[rpcl rl]|] eqn:E.
  - exploit handler_correct_succeed; eauto.
    intros H'. specialize (H' HIT E).
    destruct H' as (m2' & zr & zrpc & ESCAPE1 & MATCH').
    exploit rte_success; eauto.
    intros ESCAPE2.
    generalize (runsToEscape_determ ESCAPE1 ESCAPE2).
    intros. subst. eauto.
    econstructor; eauto.
    + eapply handler_final_mem_meminj; eauto.
    + cut (valid_update m2 m2'); eauto using match_stacks_valid_update.
      constructor; eauto.
      * unfold mem_def_on_cache, cupd in *.
        eapply Mem.upd_frame_defined; eauto.
      * intros b fr KERNEL NEQ FRAME.
        assert (FRAME' : Mem.get_frame mem b = Some fr).
        { unfold cupd in MEM.
          rewrite <- FRAME.
          eapply get_frame_upd_frame_neq; eauto. }
        destruct MATCH' as (mem' & EXT & ? & ? & ? & [? EQ] & ?).
        apply EQ; eauto.
    + assert (labToVal pcl pct0 mem); eauto.
      destruct MATCH' as (mem' & EXT & ? & ? & ? & [_ EQ] & ?).
      assert (mem_def_on_cache cblock mem).
      { unfold cupd in MEM.
        unfold mem_def_on_cache.
        erewrite get_frame_upd_frame_eq; eauto. }
      assert (mem_def_on_cache cblock mem') by (eauto using extends_mem_def_on_cache).
      assert (labToVal pcl pct0 mem') by (eauto using labToVal_extension_comp).
      eapply labToVal_cache; eauto.
      constructor; eauto.
  - exploit handler_correct_fail; eauto.
    intros H.
    destruct H as (st & m2' & ESCAPE1 & EXT).
    inv ESCAPE1.
    + apply runsUntilUser_r in STAR. simpl in STAR. congruence.
    + exfalso.
      eapply kernel_run_success_fail_contra; eauto.
Qed.

(** Notions of concrete executions for proving this refinement *)
Section CExec.

(* congruence fails if this is let-bound *)
Local Notation ctrace := (list CEvent).

Inductive exec_end : CS -> CS -> Prop :=
| ee_refl : forall s, exec_end s s
| ee_kernel_end : forall s s', runsToEnd cblock ctable s s' -> exec_end s s'
| ee_final_fault : forall s s' s'',
                     priv s = false ->
                     cstep cblock ctable s Silent s' ->
                     runsToEnd cblock ctable s' s'' ->
                     exec_end s s''.
Hint Constructors exec_end : core.

Inductive cexec : CS -> ctrace -> CS -> Prop :=
| ce_end : forall s s', exec_end s s' -> cexec s nil s'
| ce_kernel_begin : forall s s' t s'',
                      runsUntilUser cblock ctable s s' ->
                      cexec s' t s'' ->
                      cexec s t s''
| ce_user_hit : forall s e s' t s'',
                  priv s = false ->
                  cstep cblock ctable s e s' ->
                  priv s' = false ->
                  cexec s' t s'' ->
                  cexec s (op_cons e t) s''
| ce_user_miss : forall s s' s'' t s''',
                   priv s = false ->
                   cstep cblock ctable s Silent s' ->
                   runsUntilUser cblock ctable s' s'' ->
                   cexec s'' t s''' ->
                   cexec s t s'''.
Hint Constructors cexec : core.

Lemma exec_end_step : forall s e s' s''
                             (STEP : cstep cblock ctable s e s')
                             (EXEC : exec_end s' s''),
                        cexec s (op_cons e nil) s''.
Proof.
  intros.
  destruct (priv s) eqn:PRIV;
  [exploit priv_no_event_l; eauto; intros ?; subst|];
  (destruct (priv s') eqn:PRIV';
  [exploit priv_no_event_r; eauto; intros ?; subst|]);
  inv EXEC; eauto.
Qed.
Hint Resolve exec_end_step : core.

Lemma cexec_step : forall s e s' t s''
                          (Hstep : cstep cblock ctable s e s')
                          (Hexec : cexec s' t s''),
                          cexec s (op_cons e t) s''.
Proof.
  intros.
  inv Hexec; simpl; eauto;
  (destruct (priv s) eqn:PRIV;
   [assert (e = Silent) by (eapply priv_no_event_l; eauto); subst|]);
  eauto.
  - exploit priv_no_event_r; eauto.
    intros ?. subst.
    eauto.
  - subst. simpl.
    eapply ce_kernel_begin; eauto.
Qed.

Lemma exec_cexec : forall s t s',
                     TINI.exec (cstep cblock ctable) s t s' ->
                     cexec s t s'.
Proof.
  intros s t s' Hexec.
  induction Hexec; eauto.
  - eapply cexec_step with (e := E e); eauto.
  - eapply cexec_step with (e := Silent); eauto.
Qed.

End CExec.

Lemma is_syscall_dec :
  forall s2,
    (forall id, read_m (fst (pc s2)) (imem s2) <> Some (SysCall id)) \/
    exists id, read_m (fst (pc s2)) (imem s2) = Some (SysCall id).
Proof.
  intros.
  destruct (read_m (fst (pc s2)) (imem s2)) as [instr|]; try (left; congruence).
  destruct instr; eauto; try (left; congruence).
Qed.

Variable kc : list Instr.

Definition match_systables :=
  forall sa sc ca sc' sc'' id
         (MATCH : match_states kc sa sc)
         (INSTR : read_m (fst (pc sc)) (imem sc) = Some (SysCall id))
         (STEP : cstep cblock ctable sc ca sc')
         (RUN : runsUntilUser cblock ctable sc' sc''),
  exists sa' aa,
    step_rules fetch_rule atable sa aa sa'
    /\ match_states kc sa' sc''
    /\ match_actions aa ca.

Hypothesis Hmatch_systables : match_systables.

Lemma quasi_abstract_concrete_sref_prop :
  state_refinement_statement (step_rules fetch_rule atable)
                             (cstep cblock ctable)
                             (match_states kc) match_events.
Proof.
  intros s1 s2 t2 s2' MATCH EXEC. simpl.
  apply exec_cexec in EXEC.
  match type of EXEC with
    | cexec _ ?T _ =>
      remember T as t2'
  end.
  gdep t2. gdep s1.
  unfold remove_none.
  induction EXEC; intros s1 MATCH t2 Ht2; unfold remove_none.
  - exists nil. exists s1.
    split. constructor.
    constructor.
  - inv MATCH.
    apply runsUntilUser_l in H.
    inv H.
  - exploit cache_hit_simulation; eauto.
    intros [e1 [s1' [STEP [ME MS]]]].
    exploit IHEXEC; eauto.
    intros [t1 [? [? ?]]].
    exists (op_cons e1 t1). eexists.
    split. destruct e1; econstructor; eauto.

    simpl.
    inv ME; simpl; eauto.
  - destruct (is_syscall_dec s) as [NOTSYSCALL | [id EQ]].
    + exploit cache_miss_simulation; eauto.
    + exploit Hmatch_systables; eauto.
      intros (s1' & ? & STEP & STATES & ACTIONS). inv ACTIONS.
      exploit IHEXEC; eauto.
      intros (t1 & s1'' & EXEC' & MATCH'). eauto.
Qed.

Definition quasi_abstract_concrete_sref :=
  {| sref_prop := quasi_abstract_concrete_sref_prop |}.

End StateRefinement.

Require Import CodeTriples.

Section CorrectImpl.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}.

Variable cblock : FaultRoutine.block.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.
Variable atable : ASysTable T.
Variable ctable_impl : list CSysCallImpl.

Variable fetch_rule :
  forall opcode : OpCode, AllowModify (labelCount opcode).
Variable faultHandler : list Instr.
Let ctable := build_syscall_table (Z.of_nat (length faultHandler)) ctable_impl.
Hypothesis handler_correct_succeed :
  handler_spec_succeed cblock ctable _ fetch_rule faultHandler.
Hypothesis handler_correct_fail :
  handler_spec_fail cblock ctable _ fetch_rule faultHandler.

Let match_atoms S := match_atoms T (val privilege) S privilege match_tags.

Definition csyscall_impl_correct (asc : ASysCall T) csc : Prop :=
  asi_arity asc = fst csc /\
  forall S (Q : memory -> stack -> Prop),
    HT cblock ctable (snd csc)
       (fun m s =>
          exists mi aargs cargs s0,
            s = map CData cargs ++ s0 /\
            length cargs = asi_arity asc /\
            mem_def_on_cache cblock m /\
            Forall2 (fun aa ca => match_atoms mi aa ca m) aargs cargs /\
            (forall m' ares cres tres,
               user_memory_extension m m' ->
               (forall b fr, Mem.stamp b = Kernel ->
                             Mem.get_frame m b = Some fr ->
                             Mem.get_frame m' b = Some fr) ->
               asi_sem asc aargs = Some ares ->
               @match_atoms S mi ares cres m' ->
               Q m' ((Vint 1, tres) ::: cres ::: s0)) /\
            (forall m' tres,
               asi_sem asc aargs = None ->
               Q m' ((Vint 0, tres) ::: s0)))
       Q.

Lemma csyscall_impl_correct_ht :
  forall S asc csc raddr (Q : memory -> stack -> Prop * Outcome),
    csyscall_impl_correct asc csc ->
    HTEscape cblock ctable raddr (snd csc ++ CodeGen.genSysVRet)
             (fun m s =>
                exists mi aargs cargs s0,
                  s = map CData cargs ++ CRet raddr true false :: s0 /\
                  length cargs = asi_arity asc /\
                  mem_def_on_cache cblock m /\
                  Forall2 (fun aa ca => match_atoms mi aa ca m) aargs cargs /\
                  (forall m' ares cres,
                     user_memory_extension m m' ->
                     (forall b fr, Mem.stamp b = Kernel ->
                                   Mem.get_frame m b = Some fr ->
                                   Mem.get_frame m' b = Some fr) ->
                     asi_sem asc aargs = Some ares ->
                     @match_atoms S mi ares cres m' ->
                     let (prop, outcome) := Q m' (cres ::: s0) in
                     prop /\ outcome = Success) /\
                  (forall m',
                     asi_sem asc aargs = None ->
                     let (prop, outcome) := Q m' (CRet raddr true false :: s0) in
                     prop /\ outcome = Failure))
             Q.
Proof.
  intros.
  eapply HTEscape_compose_flip.
  { eapply CodeSpecs.genSysVRet_spec. }
  eapply HT_strengthen_premise.
  { apply H. }
  intros m s (mi & aargs & cargs & s0 & ? & ARITY & MEM & ARGS & SUCC & FAIL). subst.
  repeat (eexists; eauto).
  - intros. exploit SUCC; eauto 7.
  - intros. exploit FAIL; eauto.
Qed.

Definition ctable_impl_correct : Prop :=
  forall id csc
         (FETCH : index_list id ctable_impl = Some csc),
  exists asc,
    atable id = Some asc /\
    csyscall_impl_correct asc csc.

End CorrectImpl.

Section Ref.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}.

Variable cblock : FaultRoutine.block.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.
Variable atable : ASysTable T.
Variable ctable_impl : list CSysCallImpl.

Variable fetch_rule :
  forall opcode : OpCode, AllowModify (labelCount opcode).
Variable faultHandler : list Instr.
Let ctable := build_syscall_table (Z.of_nat (length faultHandler)) ctable_impl.
Hypothesis handler_correct_succeed :
  handler_spec_succeed cblock ctable _ fetch_rule faultHandler.
Hypothesis handler_correct_fail :
  handler_spec_fail cblock ctable _ fetch_rule faultHandler.

Let match_atoms := match_atoms T (val privilege) unit privilege match_tags.

Context {WFCLatt: WfConcreteLattice cblock ctable T Latt CLatt}.

Lemma ctable_fetch_inv_gen :
  forall id csc
         (SYSC : ctable id = Some csc),
  exists cti code cti',
    ctable_impl = cti ++ (csi_arity csc, code) :: cti' /\
    length cti = id /\
    csi_pc csc = Z.of_nat (length (build_kernel_code faultHandler cti)).
Proof.
  subst ctable.
  clear.
  gdep faultHandler. clear faultHandler.
  induction ctable_impl as [|[arity code] cti' IH];
  intros kernel; intros.
  - destruct id; inversion SYSC.
  - destruct id; simpl in SYSC.
    * eexists nil, code, cti'.
      inv SYSC. eauto.
    * rewrite <- Nat2Z.inj_add in SYSC.
      rewrite <- app_length in SYSC.
      apply IH in SYSC.
      destruct SYSC as (cti & code' & cti'' & ? & ? & PC). subst.
      eexists ((arity, code) :: cti).
      repeat eexists; eauto.
Qed.

Lemma build_kernel_code_app_aux :
  forall c1 c2 scs,
    build_kernel_code (c1 ++ c2) scs = c1 ++ build_kernel_code c2 scs.
Proof.
  intros. gdep c1. gdep c2.
  induction scs as [|sc scs IH]; intros; simpl; eauto.
  rewrite <- IH.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma build_kernel_code_app :
  forall c scs1 scs2,
    build_kernel_code c (scs1 ++ scs2) =
    build_kernel_code c scs1 ++ build_kernel_code nil scs2.
Proof.
  intros.
  rewrite <- build_kernel_code_app_aux.
  rewrite app_nil_r.
  unfold build_kernel_code.
  rewrite fold_left_app.
  reflexivity.
Qed.

Lemma ctable_fetch_inv :
  forall id csc
         (SYSC : ctable id = Some csc),
  exists code,
    index_list id ctable_impl = Some (csi_arity csc, code) /\
    code_at (csi_pc csc) (build_kernel_code faultHandler ctable_impl) (code ++ CodeGen.genSysVRet).
Proof.
  clear.
  intros.
  apply ctable_fetch_inv_gen in SYSC.
  destruct SYSC as (cti & code & cti' & ? & ? & PC). subst.
  eexists. split; eauto using index_list_app'.
  rewrite build_kernel_code_app.
  simpl.
  eapply code_at_compose_1.
  erewrite <- (build_kernel_code_app_aux (code ++ CodeGen.genSysVRet) nil).
  rewrite app_nil_r.
  eapply code_at_app.
  assumption.
Qed.

Hypothesis Hctable_impl_correct : ctable_impl_correct cblock atable ctable_impl faultHandler.

Notation meminj := (meminj unit privilege).
Notation Meminj := (Meminj T (val privilege) unit privilege match_tags).
Notation match_atoms := (match_atoms T (val privilege) unit privilege match_tags).
Notation match_vals := (match_vals unit privilege).
Notation update_meminj := (update_meminj unit privilege).

Definition ac_match_initial_stack_data stkdata1 stkdata2 mem :=
  Forall2 (fun a1 a2 => pcatom_labToVal a1 a2 mem) stkdata1 stkdata2.

Inductive ac_match_initial_data :
  abstract_init_data T ->
  concrete_init_data -> Prop :=
| ac_mid : forall prog mem stkdata1 stkdata2 def1 def2
                  (UP2DATE : cache_up2date cblock fetch_rule mem)
                  (DATA : ac_match_initial_stack_data stkdata1 stkdata2 mem)
                  (DEF : labToVal def1 def2 mem),
             ac_match_initial_data
               (prog, stkdata1, def1)
               (prog, mem, stkdata2, def2).

(* Maybe move this later *)
Definition emptyinj : meminj := fun _ => None.
Hint Unfold emptyinj : core.

Lemma emptyinj_meminj : forall mem, Meminj (Mem.empty _ _) mem emptyinj.
Proof.
  unfold emptyinj.
  constructor; simpl; congruence.
Qed.
Hint Resolve emptyinj_meminj : core.

Lemma emptyinj_userinj : Userinj emptyinj.
Proof.
  constructor; simpl; auto.
Qed.
Hint Resolve emptyinj_userinj : core.

Lemma match_init_stacks:
  forall stkdata1 stkdata2 mem
         (STKDATA : ac_match_initial_stack_data stkdata1 stkdata2 mem),
    match_stacks emptyinj
                 (map (fun a : PcAtom T => let (i,l) := a in AData (Vint i,l)) stkdata1)
                 (map (fun a : PcAtom (val privilege) => let (i,l) := a in CData (Vint i,l)) stkdata2) mem.
Proof.
  induction 1 as [|[xv1 xl1] [xv2 xl2] sd1 sd2 [H1 H2]];
  intros;
  repeat (simpl fst in *; subst; constructor; auto).
Qed.
Hint Resolve match_init_stacks : core.

Lemma ac_match_initial_data_match_initial_states :
  forall ai ci,
    ac_match_initial_data ai ci ->
    match_states cblock
                 fetch_rule faultHandler
                 (build_kernel_code faultHandler ctable_impl)
                 (init_state (quasi_abstract_machine fetch_rule atable) ai)
                 (init_state (concrete_machine cblock faultHandler ctable_impl) ci).
Proof.
  intros ai ci H. inv H.
  simpl in *.
  econstructor; eauto.
  rewrite <- (app_nil_r faultHandler) at 1.
  rewrite build_kernel_code_app_aux.
  eauto using code_at_compose_1, code_at_id.
Qed.

Lemma match_stacks_all_data_map :
  forall mi aargs' cargs m2,
    match_stacks mi aargs' (map CData cargs) m2 ->
    exists aargs,
      aargs' = map AData aargs /\
      Forall2 (fun aa ca => match_atoms mi aa ca m2) aargs cargs.
Proof.
  intros mi aargs' cargs m2 H.
  gdep aargs'.
  induction cargs as [|ca cargs IH]; simpl; intros aargs' H.
  - inv H. exists nil. eauto.
  - inversion H as [|ase ca' aargs'' cargs' STKELMT STKS]. subst. clear H.
    inversion STKELMT as [aa ca' m2' ATOMS|]. subst. clear STKELMT.
    apply IH in STKS. destruct STKS as (aargs & ? & ARGS). subst.
    eexists. split; eauto. simpl; eauto.
Qed.

Lemma Forall2_length :
  forall T S (R : T -> S -> Prop)
         l1 l2,
    Forall2 R l1 l2 -> length l1 = length l2.
Proof. induction 1; simpl; eauto. Qed.

Lemma HTEscape_elim :
  forall P raddr c Q s1 s2 n
         (SPEC : CodeTriples.HTEscape cblock ctable raddr
                                      c P Q)
         (PRE : P (mem s1) (stk s1))
         (CODE : CodeTriples.code_at n (fhdl s1) c)
         (RUNS : runsToEscape cblock ctable s1 s2)
         (PC : pc s1 = (n, handlerTag))
         (PRIV : priv s1 = true),
    let (prop, outcome) := Q (mem s2) (stk s2) in
    prop /\
    CodeTriples.predicted_outcome outcome raddr (pc s2) (priv s2) /\
    imem s1 = imem s2 /\
    fhdl s1 = fhdl s2.
Proof.
  intros.
  destruct s1. simpl in *. subst.
  exploit SPEC; eauto.
  intros (stk1 & mem1 & pc1 & priv1 & POST).
  destruct (Q mem1 stk1) as [prop outcome] eqn:HQ.
  destruct POST as (POST & OUTCOME & RUNS').
  assert (E := runsToEscape_determ RUNS RUNS'). subst. simpl in *.
  rewrite HQ. eauto.
Qed.

Lemma Forall2_weaken :
  forall T S (R R' : T -> S -> Prop) l1 l2
         (WEAKER : forall t s, R t s -> R' t s)
         (FORALL : Forall2 R l1 l2),
    Forall2 R' l1 l2.
Proof. intros. induction FORALL; eauto. Qed.

Lemma syscall_extends :
  forall m2 m2'
         (USERMEM : user_memory_extension m2 m2')
         (KERNELMEM : forall b fr,
                        Mem.stamp b = Kernel ->
                        Mem.get_frame m2 b = Some fr ->
                        Mem.get_frame m2' b = Some fr),
    extends m2 m2'.
Proof.
  intros.
  intros b2 fr H.
  destruct (Mem.stamp b2) eqn:STAMP; eauto.
Qed.
Hint Resolve syscall_extends : core.

Lemma match_atoms_syscall :
  forall m1 m2 m2' mi
         (DEF : mem_def_on_cache cblock m2)
         (MEMINJ : Meminj m1 m2 mi)
         (USERMEM : user_memory_extension m2 m2')
         (KERNELMEM : forall b fr,
                        Mem.stamp b = Kernel ->
                        Mem.get_frame m2 b = Some fr ->
                        Mem.get_frame m2' b = Some fr),
    forall aa ca,
      match_atoms mi aa ca m2 ->
      match_atoms mi aa ca m2'.
Proof.
  intros.
  inv H.
  constructor; eauto.
  eapply labToVal_extension_comp; eauto.
Qed.

Lemma meminj_syscall :
  forall m1 m2 m2' mi
         (DEF : mem_def_on_cache cblock m2)
         (MEMINJ : Meminj m1 m2 mi)
         (USERMEM : user_memory_extension m2 m2')
         (KERNELMEM : forall b fr,
                        Mem.stamp b = Kernel ->
                        Mem.get_frame m2 b = Some fr ->
                        Mem.get_frame m2' b = Some fr),
    Meminj m1 m2' mi.
Proof.
  intros.
  constructor.
  - intros b1 b2 INJ.
    exploit mi_valid; eauto.
    intros (f1 & f2 & FRAME1 & FRAME2 & MATCH).
    eexists f1, f2.
    split; eauto.
    split.
    + eapply syscall_extends; eauto.
    + eapply Forall2_weaken; eauto.
      simpl. eapply match_atoms_syscall; eauto.
  - intros.
    eapply mi_invalid; eauto.
    destruct (Mem.stamp b2) eqn:STAMP.
    + destruct (Mem.get_frame m2 b2) as [fr|] eqn:FRAME; trivial.
      apply USERMEM in FRAME; eauto.
      congruence.
    + destruct (Mem.get_frame m2 b2) as [fr|] eqn:FRAME; trivial.
      apply KERNELMEM in FRAME; eauto.
      congruence.
  - eapply mi_inj; eauto.
Qed.

Lemma cache_up2date_syscall :
  forall m2 m2'
         (CACHE : cache_up2date cblock fetch_rule m2)
         (USERMEM : user_memory_extension m2 m2')
         (KERNELMEM : forall b fr,
                        Mem.stamp b = Kernel ->
                        Mem.get_frame m2 b = Some fr ->
                        Mem.get_frame m2' b = Some fr),
    cache_up2date cblock fetch_rule m2'.
Proof.
  intros.
  inv CACHE.
  constructor.
  - eauto using extends_mem_def_on_cache.
  - intros.
    eapply cache_hit_mem_extends_inv in H; eauto.
    apply UP2DATE in H.
    destruct H as (vls & pcl & rpcl & rpct & rl & rt & H1 & H2 & H3 & H4 & H5 & H6).
    eapply cache_hit_read_mem_extends in H6; eauto.
    repeat eexists; eauto using labToVal_extension_comp, labsToVals_extension_comp.
Qed.

Lemma match_systables_from_impl :
  match_systables cblock ctable fetch_rule faultHandler atable (build_kernel_code faultHandler ctable_impl).
Proof.
  intros sa sc ca sc' sc'' id MATCH INSTR STEP RUN.
  exploit configuration_at_syscall; eauto.
  { destruct MATCH. reflexivity. }
  clear STEP.
  intros (id' & entry & cargs & sc0 & INSTR' & TABLE &
          MEM & FHDL & IMEM & STK' & STK & PC & PRIV & SILENT).
  assert (id' = id) by congruence. subst id'. clear INSTR'.
  assert (PRIV'' : priv sc'' = false) by (eauto using runsUntilUser_l).
  destruct sc as [mem fhdl imem stk pc priv].
  destruct sc' as [mem' fhdl' imem' stk' pc' priv']. simpl in *.
  subst fhdl' mem' imem' stk' pc' priv' ca.
  apply ctable_fetch_inv in TABLE. simpl in TABLE.
  destruct TABLE as (code & FETCH & CODE).
  apply Hctable_impl_correct in FETCH.
  destruct FETCH as (asc & FETCH & CORRECT).
  inv MATCH. simpl in *. subst.
  exploit match_stacks_app; eauto.
  intros (aargs' & astk & ? & STKS & REST). subst.
  apply match_stacks_all_data_map in STKS.
  destruct STKS as (aargs & ? & ARGS). subst.
  assert (CORRECT' :=
            csyscall_impl_correct_ht (S := unit)
                                     (pcv + 1, pct)
                                     (fun m' s' => match asi_sem asc aargs with
                                                    | Some ares =>
                                                      (exists cres,
                                                         match_atoms mi ares cres m' /\
                                                         s' = cres ::: sc0 /\
                                                         extends mem m' /\
                                                         cache_up2date cblock fetch_rule m' /\
                                                         Meminj m1 m' mi /\
                                                         (forall aa ca,
                                                            match_atoms mi aa ca mem ->
                                                            match_atoms mi aa ca m'),
                                                         Success)
                                                    | None => (True, Failure)
                                                  end)
                                     CORRECT).
  simpl in CORRECT'. apply rte_success in RUN.
  exploit HTEscape_elim; eauto; simpl; eauto; clear CORRECT' RUN.
  { simpl.
    do 4 eexists. repeat (split; eauto).
    - destruct CORRECT. simpl in *. congruence.
    - inv CACHE. eauto.
    - intros m' ares cres USERMEM KMEM RES MATCH.
      rewrite RES.
      split; trivial.
      eexists. do 2 (split; eauto). inv CACHE.
      split; eauto.
      split; eauto using cache_up2date_syscall, cu2d_intro.
      split; eauto using meminj_syscall, match_atoms_syscall.
    - intros m' RES. rewrite RES. auto. }
  destruct (asi_sem asc aargs) as [ares|] eqn:RES. simpl.
  - intros ((cres & MATCHRES & STK'' & EXT & CACHE' & MINJ'' & MATCHATOMS) & [? ?] & ? & ?).
    destruct sc'' as [mem'' fhdl'' imem'' stk'' pc'' priv'']. simpl in *.
    subst priv'' pc'' imem'' fhdl'' stk''.
    do 2 eexists.
    repeat split; try eapply step_syscall; try constructor; eauto.
    + destruct CORRECT as [ARITY _].
      rewrite ARITY. simpl.
      eauto using Forall2_length.
    + unfold match_atoms, match_stacks in *.
      inv CACHE.
      econstructor; eauto using labToVal_extension_comp.
      constructor; try econstructor; eauto.
      eapply Forall2_weaken; eauto.
      simpl.
      intros ase cse STKELMT.
      inv STKELMT; constructor; eauto using labToVal_extension_comp.
  - simpl in *. intuition. congruence.
Qed.

Definition quasi_abstract_concrete_ref :
  refinement (quasi_abstract_machine fetch_rule atable)
             (concrete_machine cblock faultHandler ctable_impl) :=
  refinement_from_state_refinement (quasi_abstract_machine fetch_rule atable)
                                   (concrete_machine cblock faultHandler ctable_impl)
                                   (quasi_abstract_concrete_sref stamp_cblock
                                                                 handler_correct_succeed
                                                                 handler_correct_fail
                                                                 match_systables_from_impl)
                                   ac_match_initial_data
                                   ac_match_initial_data_match_initial_states.

End Ref.
