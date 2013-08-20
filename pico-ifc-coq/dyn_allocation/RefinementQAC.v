Require Import EquivDec.
Require Import List.
Require Import ZArith.

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

Section Refinement.

Variable cblock : FaultRoutine.block.
Hypothesis stamp_cblock : Mem.stamp cblock = Kernel.

Context {T: Type}
        {Latt: JoinSemiLattice T}
        {CLatt: ConcreteLattice T}
        {WFCLatt: WfConcreteLattice cblock T Latt CLatt}.

Definition match_tags l t := t = labToZ l.
Notation meminj := (meminj unit privilege).
Notation Meminj := (Meminj T Z unit privilege match_tags).
Notation match_atoms := (match_atoms T Z unit privilege match_tags).
Notation match_vals := (match_vals unit privilege).
Notation update_meminj := (update_meminj unit privilege).

Hint Resolve match_vals_eq.
Hint Constructors Memory.match_atoms.
Hint Constructors Memory.match_vals.
Hint Resolve update_meminj_eq.

Record Userinj (mi : meminj) : Prop := {

  ui_no_kernel : forall b2, Mem.stamp b2 = Kernel ->
                            mi b2 = None

}.

Lemma userinj_alloc : forall mi z m1 a1 b1 m1' m2 a2 b2 m2',
                      forall (MINJ : Meminj m1' m2' (update_meminj mi b2 b1))
                             (UINJ : Userinj mi)
                             (ALLOC1 : qa_alloc z a1 m1 = Some (b1, m1'))
                             (ALLOC2 : c_alloc User z a2 m2 = Some (b2, m2'))
                             (ATOMS : match_atoms mi a1 a2),
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

Inductive match_stk_elmt (mi : meminj) : StkElmt T unit -> CStkElmt -> Prop :=
| mse_data : forall a1 a2
                    (ATOMS : match_atoms mi a1 a2),
               match_stk_elmt mi (AData a1) (CData a2)
| mse_ret : forall pcv pcl b, match_stk_elmt mi (ARet (pcv,pcl) b) (CRet (pcv, labToZ pcl) b false).
Hint Constructors match_stk_elmt.

Definition match_stacks (mi : meminj) : list (StkElmt T unit) -> list CStkElmt -> Prop :=
  Forall2 (match_stk_elmt mi).
Hint Unfold match_stacks.

Variable fetch_rule_g :
  forall opcode : OpCode, AllowModify (labelCount opcode).
Definition fetch_rule_impl : OpCode -> {n : nat & AllowModify n} :=
  fun o => existT _ (labelCount o) (fetch_rule_g o).

Definition faultHandler := FaultRoutine.faultHandler fetch_rule_impl.

Inductive cache_up2date m : Prop :=
| cu2d_intro :
    forall cache
           (FRAME : Mem.get_frame m cblock = Some cache)
           (UP2DATE : forall opcode vls pcl,
                        cache_hit cache (opCodeToZ opcode) (labsToZs vls) (labToZ pcl) ->
                        match apply_rule (fetch_rule_g opcode) pcl vls with
                          | Some (rpcl,rl) => cache_hit_read_mem cblock m (labToZ rl) (labToZ rpcl)
                          | None => False
                        end),
      cache_up2date m.

Inductive match_states : @qa_state T -> CS -> Prop :=
| qac_intro : forall mi m1 m2 p stk1 stk2 pcv pcl
                     (MINJ : Meminj m1 m2 mi)
                     (UINJ : Userinj mi)
                     (STK : match_stacks mi stk1 stk2)
                     (CACHE : cache_up2date m2),
                match_states (AState m1 p stk1 (pcv,pcl))
                             (CState m2 faultHandler p stk2 (pcv,labToZ pcl) false).
Hint Constructors match_states.

Lemma alloc_match_stacks :
  forall size
         a1 m1 b1 m1'
         a2 m2 b2 m2'
         mi stk1 stk2
         (STK : match_stacks mi stk1 stk2)
         (ALLOC1 : qa_alloc size a1 m1 = Some (b1, m1'))
         (ALLOC2 : c_alloc User size a2 m2 = Some (b2, m2'))
         (INJ : Meminj m1 m2 mi),
    match_stacks (update_meminj mi b2 b1) stk1 stk2.
Proof.
  intros.
  induction STK; constructor; trivial.
  inv H; constructor.
  inv ATOMS. constructor; auto.
  inv VALS; constructor; trivial.
  rewrite update_meminj_neq; eauto.
  eapply mi_valid in BLOCK; eauto.
  destruct BLOCK as [? [? [? [? ?]]]].
  unfold c_alloc, alloc in ALLOC2.
  destruct (zreplicate size a2); inv ALLOC2.
  eapply Mem.alloc_get_fresh in H3; eauto.
  congruence.
Qed.

Lemma match_stacks_app :
  forall mi stk1 args2 stk2'
         (STKS : match_stacks mi stk1 (args2 ++ stk2')),
    exists args1 stk1',
      stk1 = args1 ++ stk1' /\
      match_stacks mi args1 args2 /\
      match_stacks mi stk1' stk2'.
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
  forall mi stk1 stk2
         (STKS : match_stacks mi stk1 stk2),
    length stk1 = length stk2.
Proof. induction 1; simpl; eauto. Qed.
Hint Resolve match_stacks_length.

Lemma match_stacks_all_data :
  forall mi stk1 stk2
         (STKS : match_stacks mi stk1 stk2)
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
Hint Resolve match_stacks_all_data.

Lemma match_stacks_app_2 :
  forall mi stk11 stk12 stk21 stk22
         (STKS1 : match_stacks mi stk11 stk21)
         (STKS2 : match_stacks mi stk12 stk22),
    match_stacks mi (stk11 ++ stk12) (stk21 ++ stk22).
Proof. intros. eauto using Forall2_app. Qed.
Hint Resolve match_stacks_app_2.

Hint Constructors pop_to_return.

Lemma match_stacks_pop_to_return :
  forall mi stk1 stk2 stk2' pcv cpcl b p
         (STKS : match_stacks mi stk1 stk2)
         (POP : c_pop_to_return stk2 (CRet (pcv, cpcl) b p :: stk2')),
    exists pcl stk1',
      cpcl = labToZ pcl /\
      pop_to_return stk1 (ARet (pcv, pcl) b :: stk1') /\
      match_stacks mi stk1' stk2'.
Proof.
  intros.
  gdep stk2.
  induction stk1 as [|se1 stk1 IH]; intros;
  inv POP; inv STKS;
  match goal with
    | H : match_stk_elmt _ _ _ |- _ =>
      inv H; eauto
  end.
  exploit IH; eauto.
  intros [? [? [? [? ?]]]]; subst.
  eauto 7.
Qed.

Lemma match_stacks_index_list :
  forall mi n s1 s2 x2
         (IDX : index_list n s2 = Some x2)
         (STKS : match_stacks mi s1 s2),
    exists x1,
      index_list n s1 = Some x1 /\
      match_stk_elmt mi x1 x2.
Proof.
  induction n as [|n IH]; intros; inv STKS; simpl in *; allinv; eauto.
Qed.

Lemma match_stacks_update_list :
  forall mi n se1 s1 se2 s2 s2'
         (STKS : match_stacks mi s1 s2)
         (STKELMTS : match_stk_elmt mi se1 se2)
         (UPD : update_list n se2 s2 = Some s2'),
    exists s1',
      update_list n se1 s1 = Some s1' /\
      match_stacks mi s1' s2'.
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
  forall mi n s1 s2 s2'
         (SWAP : swap n s2 = Some s2')
         (STKS : match_stacks mi s1 s2),
    exists s1',
      swap n s1 = Some s1' /\
      match_stacks mi s1' s2'.
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

Definition pcatom_labToZ (a:PcAtom T) : (PcAtom Z) :=
  let (v,l) := a in (v,labToZ l).

Definition pcatom_ZToLab (a:PcAtom Z) : (PcAtom T) :=
  let (v,l) := a in (v,ZToLab l).

Lemma atom_ZToLab_labToZ_id: forall (a:PcAtom T), a = pcatom_ZToLab (pcatom_labToZ a).
Proof.
  intros. unfold pcatom_labToZ, pcatom_ZToLab. destruct a. f_equal.
  eapply ZToLab_labToZ_id; eauto.
Qed.

Lemma opCodeToZ_inj: forall o1 o2, opCodeToZ o1 = opCodeToZ o2 -> o1 = o2.
Proof.
  intros o1 o2 Heq.
  destruct o1, o2; inv Heq; try congruence.
Qed.

Open Scope nat_scope.

Lemma labsToZs_cons_hd: forall n0 a v0 b v3,
  S n0 <= 3 ->
  labsToZs (Vector.cons T a n0 v0) = labsToZs (Vector.cons T b n0 v3) ->
  a = b.
Proof.
  intros.  inv H0.
  unfold nth_labToZ in H2. destruct (le_lt_dec (S n0) 0).  inv l.
  unfold Vector.nth_order in H2. simpl in H2.
  apply labToZ_inj with (cblock := cblock) (J := Latt) in H2; auto.
Qed.

Lemma nth_labToZ_cons:
  forall nth n a v,
    nth_labToZ (Vector.cons T a n v) (S nth) = nth_labToZ v nth.
Proof.
  induction n; intros.
  - unfold nth_labToZ.
    case_eq (le_lt_dec (S nth) 1); case_eq (le_lt_dec nth 0); intros; auto;
    try (zify ; omega).
  - unfold nth_labToZ.
    case_eq (le_lt_dec (S (S n)) (S nth)); case_eq (le_lt_dec (S n) nth); intros; auto;
    try (zify ; omega).
    unfold Vector.nth_order. simpl. symmetry.
    erewrite of_nat_lt_proof_irrel ; eauto.
Qed.

Lemma labsToZs_cons_tail:
  forall n0 a v0 b v3,
    (n0 <= 2)%nat ->
    labsToZs (Vector.cons T a n0 v0) = labsToZs (Vector.cons T b n0 v3) ->
    labsToZs v0 = labsToZs v3.
Proof.
  intros. inv H0.
  unfold labsToZs.
  repeat (rewrite nth_labToZ_cons in H3). inv H3. clear H1.
  repeat (rewrite nth_labToZ_cons in H4). inv H4. clear H1.
  replace (nth_labToZ v0 2) with (nth_labToZ v3 2).
  auto.
  unfold nth_labToZ.
  case_eq (le_lt_dec n0 2); intros; auto.
  zify ; omega.
Qed.

Lemma labsToZs_inj: forall n (v1 v2: Vector.t T n), n <= 3 ->
     labsToZs v1 = labsToZs v2 -> v1 = v2.
Proof.
  intros n v1 v2.
  set (P:= fun n (v1 v2: Vector.t T n) => n <= 3 -> labsToZs v1 = labsToZs v2 -> v1 = v2) in *.
  eapply Vector.rect2 with (P0:= P); eauto.
  unfold P. auto.
  intros.
  unfold P in *. intros.
  exploit labsToZs_cons_hd; eauto. intros Heq ; inv Heq.
  eapply labsToZs_cons_tail in H1; eauto.
  exploit H ; eauto. zify; omega.
  intros Heq. inv Heq.
  reflexivity. zify; omega.
Qed.

Definition abstract_event (ce : CEvent) : Event T :=
  match ce with
    | CEInt ca => EInt (pcatom_ZToLab ca)
  end.

Definition concretize_event (ae : Event T) : CEvent :=
  match ae with
    | EInt aa => CEInt (pcatom_labToZ aa)
  end.

Definition match_events e1 e2 := concretize_event e1 = e2.

Definition match_actions := match_actions tini_quasi_abstract_machine
                                          (concrete_machine cblock faultHandler)
                                          match_events.

Lemma abstract_event_concretize_event :
  forall ae, abstract_event (concretize_event ae) = ae.
Proof.
  intros [[xv xl]]; simpl; auto.
  erewrite <- ZToLab_labToZ_id; eauto.
Qed.

Section RefQAC.

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
  assert (CACHE' : Mem.get_frame m' cblock = Some cache).
  { erewrite alloc_get_frame_old; eauto. }
  econstructor; eauto.
  intros.
  specialize (UP2DATE opcode vls pcl).
  unfold cache_hit_mem, cache_hit_read_mem in *.
  rewrite FRAME in *.
  rewrite CACHE' in *.
  intuition.
Qed.

Lemma store_cache_up2date :
  forall b off a m m'
         (STORE : store b off a m = Some m')
         (STAMP : Mem.stamp b = User)
         (CACHE : cache_up2date m),
    cache_up2date m'.
Proof.
  unfold store.
  intros.
  destruct CACHE.
  cut (Mem.get_frame m' cblock = Some cache).
  { intros H.
    econstructor; eauto.
    unfold cache_hit_read_mem in *.
    rewrite FRAME in *.
    rewrite H in *.
    intuition. }
  clear UP2DATE.
  destruct (Mem.get_frame m b) as [frame|] eqn:E; try congruence.
  destruct (upd_m off a frame) as [frame'|] eqn:E'; try congruence.
  erewrite Mem.get_upd_frame; eauto.
  match goal with
    | |- context[if ?b then _ else _] =>
      destruct b as [E'' | E'']; auto
  end.
  congruence.
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
Hint Resolve alloc_stamp.

Lemma analyze_cache_hit :
  forall m opcode (vls : Vector.t T (labelCount opcode)) pcl zrl zrpcl
         (UP2DATE : cache_up2date m)
         (CHIT : cache_hit_mem cblock m (opCodeToZ opcode) (labsToZs vls) (labToZ pcl))
         (CREAD : cache_hit_read_mem cblock m zrl zrpcl),
  exists rpcl rl,
    zrl = labToZ rl /\
    zrpcl = labToZ rpcl /\
    apply_rule (fetch_rule_g opcode) pcl vls = Some (rpcl, rl).
Proof.
  intros.
  destruct UP2DATE.
  unfold cache_hit_mem in *.
  rewrite FRAME in *.
  exploit UP2DATE; eauto.
  intros APPLY.
  destruct (apply_rule (fetch_rule_g opcode) pcl vls) as [[rpcl rl]|];
  try solve [intuition].
  generalize (cache_hit_read_mem_determ _ _ _ _ _ _ CREAD APPLY).
  intuition. subst. eauto.
Qed.

Ltac get_opcode :=
  match goal with
    | INST : read_m _ _ = Some ?instr |- _ =>
      let opcode := (eval compute in (opcode_of_instr instr)) in
      match opcode with
        | Some ?opcode => opcode
      end
  end.

Ltac quasi_abstract_labels opcode :=
  match goal with
    | H : context[cache_hit_mem _ _ _ ?tags _] |- _ =>
      match tags with
        | (dontCare, dontCare, dontCare) =>
          constr:(<||> : Vector.t T (labelCount opcode))
        | (labToZ ?l, dontCare, dontCare) =>
          constr:(<|l|> : Vector.t T (labelCount opcode))
        | (labToZ ?l1, labToZ ?l2, dontCare) =>
          constr:(<|l1; l2|> : Vector.t T (labelCount opcode))
        | (labToZ ?l1, labToZ ?l2, labToZ ?l3) =>
          constr:(<|l1; l2; l3|> : Vector.t T (labelCount opcode))
      end
  end.

Ltac analyze_cache_hit :=
  (* Find the current opcode, build the label vector use cache_up2date
  to build an equation about apply_rule. *)
  match goal with
    | CACHE : cache_up2date _,
      CHIT : cache_hit_mem _ _ _ _ _,
      CREAD : cache_hit_read_mem _ _ _ _ |- _ =>
      let opcode := get_opcode in
      let vls := quasi_abstract_labels opcode in
      let rpcl := fresh "rpcl'" in
      let rl := fresh "rl'" in
      generalize (@analyze_cache_hit _ _ vls _ _ _ CACHE CHIT CREAD);
      intros [rl [rpcl [? [? ?]]]]; subst
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
           | H : match_stk_elmt _ _ (CData _) |- _ => inv H
         end;
  repeat match goal with
           | H : match_atoms _ _ (?v, _) |- _ =>
             match goal with
               | H : match_vals _ _ v |- _ => fail 1
               | |- _ => inversion H; subst
             end
         end;
  repeat match goal with
           | H : match_vals _ _ (Vint _) |- _ => inv H
           | H : match_vals _ _ (Vptr _ _) |- _ => inv H
           | H : match_tags ?l ?t |- _ =>
             unfold match_tags in H; subst t
         end.

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
  inv VALS1; inv VALS2; try congruence.
  cut (b2 = b3); try congruence.
  eapply mi_inj; eauto.
Qed.
Hint Resolve match_vals_eq.

(** Cache hit case *)

Lemma cache_hit_simulation :
  forall s1 s2 a2 s2'
         (Hmatch : match_states s1 s2)
         (Hs2' : priv s2' = false)
         (Hstep : cstep cblock s2 a2 s2'),
    exists a1 s1', step_rules fetch_rule_g s1 a1 s1' /\
                   match_actions a1 a2 /\
                   match_states s1' s2'.
Proof.
  intros.
  inv Hmatch.
  unfold match_actions.
  inv Hstep; simpl in *; try congruence;

  match_inv;

  try match goal with
        | H : _ = Some Alloc,
          ALLOC : c_alloc _ _ _ _ = _,
          CACHE : cache_up2date _ |- _ =>
          exploit (meminj_alloc T Z unit privilege); eauto; try solve [constructor; eauto];
          intros [? [? [? ?]]];
          exploit userinj_alloc; eauto; intro;
          exploit alloc_match_stacks; eauto; intro;
          generalize (cache_up2date_alloc _ _ _ ALLOC CACHE); intro
      end;
  try_exploit add_defined;
  try_exploit (sub_defined unit privilege);

  try_exploit meminj_load; match_inv;

  (* For the Ret cases *)
  try_exploit match_stacks_pop_to_return;

  analyze_cache_hit;

  try match goal with
        | H : store _ _ _ _ = _ |- _ =>
          exploit (meminj_store T Z unit privilege); eauto; try solve [repeat econstructor; eauto];
          intros [? [? ?]]
      end;
  try match goal with
        | MUPDT : store _ _ _ _ = Some _,
          STAMP : Mem.stamp _ = User,
          CREAD : cache_hit_read_mem _ _ _ _ |- _ =>
          generalize (@store_cache_up2date _ _ _ _ _ MUPDT STAMP CACHE); intro
      end;

  (* For the BranchNZ case *)
  try match goal with
        | |- context[if (?z =? 0)%Z then _ else _ ] =>
          let H := fresh "H" in
          assert (H := Z.eqb_spec z 0);
          destruct (z =? 0)%Z;
          inv H
      end;

  solve [
      eexists; eexists; split; try split;
      try (econstructor (solve [compute; eauto]));
      repeat (econstructor; eauto); simpl; f_equal; intuition
    ].

Qed.

Open Scope Z_scope.

Lemma configuration_at_miss :
  forall s1 s21 e2 s22
         (MATCH : match_states s1 s21)
         (STEP : cstep cblock s21 e2 s22)
         (PRIV : priv s22 = true),
    exists opcode (vls : Vector.t T (projT1 (fetch_rule_impl opcode))),
      cupd cblock (mem s21)
           (build_cache (opCodeToZ opcode)
                        (labsToZs vls)
                        (labToZ (snd (apc s1)))) = Some (mem s22) /\
      fhdl s22 = fhdl s21 /\
      imem s22 = imem s21 /\
      stk s22 = CRet (pc s21) false false :: stk s21 /\
      pc s22 = (0, handlerTag).
Proof.
  intros.
  inv MATCH.
  inv STEP; simpl in *; try congruence; match_inv;

  (* For the Load case *)
  try_exploit meminj_load; match_inv;

  (* For the Ret cases *)
  try_exploit match_stacks_pop_to_return;

  let opcode := get_opcode in
  let vls := quasi_abstract_labels opcode in
  exists opcode; exists vls; eauto.
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
    apply mi_valid; eauto.

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
         (STEP : cstep cblock s1 e s2)
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
         (RUN1 : runsUntilUser cblock s1 s21)
         (RUN2 : runsToEnd cblock s1 s22)
         (FAIL : fst (pc s22) < 0),
    False.
Proof.
  intros.
  induction RUN1; inv RUN2;
  try match goal with
        | [ H1 : cstep _ ?s _ _,
            H2 : cstep _ ?s _ _
            |- _ ] =>
          let H := fresh "H" in
          generalize (cmach_determ H1 H2);
          intros [? ?]; subst
      end; eauto;
  try match goal with
        | [ H : runsUntilUser _ _ _ |- _ ] =>
          generalize (runsUntilUser_l H);
          intros
      end;
  try match goal with
        | [ H : runsToEnd _ _ _ |- _ ] =>
          generalize (runsToEnd_l H);
          intros
      end;
  try congruence;
  eauto using invalid_pc_no_step ; eauto.
Qed.

Lemma kernel_fail_determ :
  forall s1 s21 s22
         (RUN1 : runsToEnd cblock s1 s21)
         (FAIL1 : fst (pc s21) < 0)
         (RUN2 : runsToEnd cblock s1 s22)
         (FAIL2 : fst (pc s22) < 0),
    s21 = s22.
Proof.
  intros.
  induction RUN1; inv RUN2; trivial;
  try solve [exfalso; eauto using invalid_pc_no_step];
  try match goal with
        | [ H1 : cstep _ ?s _ _,
            H2 : cstep _ ?s _ _
            |- _ ] =>
          let H := fresh "H" in
          generalize (cmach_determ H1 H2);
          intros [? ?]; subst
      end; eauto.
Qed.

Lemma runsToEscape_determ :
  forall s1 s21 s22
         (RUN1 : runsToEscape cblock s1 s21)
         (RUN2 : runsToEscape cblock s1 s22),
    s21 = s22.
Proof.
  intros.
  inv RUN1; inv RUN2;
  eauto using runsUntilUser_determ,
              kernel_fail_determ;
  try solve [exfalso; eauto using kernel_run_success_fail_contra];
  try match goal with
        | [ H : runsUntilUser _ _ _ |- _ ] =>
          generalize (runsUntilUser_l H);
          intros
      end;
  try match goal with
        | [ H : runsToEnd _ _ |- _ ] =>
          generalize (runsToEnd_l H);
          intros
      end;
  try congruence.
Qed.

Lemma handler_final_mem_meminj :
  forall mi m1 m2 m2' rpcl rl
         (MINJ : Meminj m1 m2 mi)
         (UINJ : Userinj mi)
         (MATCH : handler_final_mem_matches cblock rpcl rl m2 m2'),
    Meminj m1 m2' mi.
Proof.
  intros.
  destruct MATCH as [_ [REST _]].
  eapply meminj_same_frames; eauto.
  intros.
  unfold update_mem_only_cache in *.
  rewrite REST; eauto.
  exploit ui_no_kernel; eauto.
  congruence.
Qed.
Hint Resolve handler_final_mem_meminj.

(* This lemma says: if the cache input matches some configuration, and
the handler runs, yielding a new memory, then that memory's cache also
matches the same configuration. *)

Lemma update_cache_spec_rvec_cache_hit :
  forall rpcl rl c m2 c' m2' op tags pc
         (MATCH : handler_final_mem_matches cblock rpcl rl m2 m2')
         (CACHE : Mem.get_frame m2 cblock = Some c)
         (CACHE' : Mem.get_frame m2' cblock = Some c')
         (HIT : cache_hit c op tags pc),
    cache_hit c' op tags pc.
Proof.
  intros.
  inv HIT;
  repeat match goal with
           | H : tag_in_mem _ _ _ |- _ =>
             inv H
           | H : tag_in_mem' _ _ _ |- _ =>
             inv H
         end.
  destruct MATCH as [RES UP].
  unfold cache_hit_read_mem in *.
  rewrite CACHE' in RES.
  destruct RES.
  destruct UP as [HH UP].
  unfold load in *.
  rewrite CACHE in UP.
  rewrite CACHE' in UP.
  econstructor; eauto; econstructor;
  try solve [rewrite <- UP; eauto; compute; omega];
  repeat match goal with
           | H : tag_in_mem _ _ _ |- _ =>
             inv H
           | H : tag_in_mem' _ _ _ |- _ =>
             inv H
         end;
  eauto.
Qed.

Lemma cache_hit_unique:
  forall c opcode opcode' labs labs' pcl pcl',
    forall
      (CHIT: cache_hit c opcode labs pcl)
      (CHIT': cache_hit c opcode' labs' pcl'),
      opcode = opcode' /\
      labs = labs' /\
      pcl = pcl'.
Proof.
  intros.
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
  forall m2 m2' opcode (vls : Vector.t T (projT1 (fetch_rule_impl opcode))) pcl rpcl rl
         (HIT : cache_hit_mem cblock m2 (opCodeToZ opcode) (labsToZs vls) (labToZ pcl))
         (OK : apply_rule (projT2 (fetch_rule_impl opcode)) pcl vls = Some (rpcl, rl))
         (MATCH : handler_final_mem_matches cblock rpcl rl m2 m2'),
    cache_up2date m2'.
Proof.
  unfold cache_hit_mem, cache_hit_read_mem.
  intros.
  destruct (Mem.get_frame m2 cblock) as [cache|] eqn:CACHE; try solve [intuition].
  assert (CACHE' : exists cache', Mem.get_frame m2' cblock = Some cache').
  { unfold handler_final_mem_matches, cache_hit_read_mem in *.
    destruct (Mem.get_frame m2' cblock); intuition.
    eauto. }
  destruct CACHE' as [cache' CACHE'].
  econstructor; eauto.
  intros opcode' vls' pcl' HIT'.
  exploit update_cache_spec_rvec_cache_hit; eauto.
  intros HIT''.
  generalize (cache_hit_unique HIT' HIT'').
  intros [E1 [E2 E3]].
  apply opCodeToZ_inj in E1. subst.
  eapply labToZ_inj in E3; eauto. subst.
  apply labsToZs_inj in E2.
  + subst.
    simpl in OK.
    rewrite OK.
    destruct MATCH. trivial.
  + destruct opcode; simpl; omega.
Qed.
Hint Resolve handler_final_mem_cache_up2date.

Lemma cache_miss_simulation :
  forall s1 s21 e21 s22 s23
         (MATCH : match_states s1 s21)
         (STEP1 : cstep cblock s21 e21 s22)
         (RUN : runsUntilUser cblock s22 s23),
    match_states s1 s23.
Proof.
  intros.
  exploit runsUntilUser_l; eauto.
  intros PRIV.
  exploit configuration_at_miss; eauto.
  intros [op [vls [DEFMEM EQS]]].
  exploit build_cache_cache_hit; eauto. intros HIT.
  inv MATCH.
  exploit build_cache_meminj; eauto. intros MINJ'.
  destruct s22. simpl in EQS.
  intuition.
  simpl in DEFMEM, MINJ', PRIV.
  subst.
  destruct (apply_rule (projT2 (fetch_rule_impl op)) pcl vls)
    as [[rpcl rl]|] eqn:E.
  - exploit handler_correct_succeed; eauto.
    intros H. specialize (H E).
    destruct H as [m2' [ESCAPE1 MATCH']].
    exploit rte_success; eauto.
    intros ESCAPE2.
    generalize (runsToEscape_determ ESCAPE1 ESCAPE2).
    intros. subst. eauto.
  - exploit handler_correct_fail; eauto.
    simpl in *.
    intros [stk' ESCAPE1].
    inv ESCAPE1.
    + apply runsUntilUser_r in STAR. simpl in STAR. congruence.
    + exfalso.
      eapply kernel_run_success_fail_contra; eauto.
Qed.

Inductive ac_match_initial_data :
  abstract_init_data T ->
  init_data (concrete_machine cblock faultHandler) -> Prop :=
| ac_mid : forall d1 p1 b1,
             ac_match_initial_data
               (p1, d1, b1)
               (p1, map pcatom_labToZ d1, labToZ b1).

(* Maybe move this later *)
Definition emptyinj : meminj := fun _ => None.
Hint Unfold emptyinj.

Lemma emptyinj_meminj : Meminj (Mem.empty _ _) (initial_memory cblock) emptyinj.
Proof.
  unfold emptyinj.
  constructor; simpl; congruence.
Qed.
Hint Resolve emptyinj_meminj.

Lemma emptyinj_userinj : Userinj emptyinj.
Proof.
  constructor; simpl; auto.
Qed.
Hint Resolve emptyinj_userinj.

Lemma match_init_stacks: forall d1,
 match_stacks emptyinj
              (map (fun a : PcAtom T => let (i,l) := a in AData (Vint i,l)) d1)
              (map (fun a : PcAtom Z => let (i,l) := a in CData (Vint i,l)) (map pcatom_labToZ d1)).
Proof.
  induction d1 as [|[xv xl] d1 IH]; intros;
  repeat (simpl; constructor; auto).
Qed.
Hint Resolve match_init_stacks.

Lemma initial_memory_up2date :
  cache_up2date (initial_memory cblock).
Proof.
  econstructor; eauto using Mem.get_init_eq.
  intros opcode vls pcl contra.
  inv contra.
  inv OP.
  inv H.
Qed.
Hint Resolve initial_memory_up2date.

Lemma ac_match_initial_data_match_initial_states :
  forall ai ci,
    ac_match_initial_data ai ci ->
    match_states (init_state (quasi_abstract_machine fetch_rule_g) ai)
                 (init_state (concrete_machine cblock faultHandler) ci).
Proof.
  intros ai ci H. inv H.
  simpl in *.
  econstructor; simpl; eauto.
Qed.

(** Notions of concrete executions for proving this refinement *)
Section CExec.

(* congruence fails if this is let-bound *)
Local Notation ctrace := (list CEvent).

Inductive exec_end : CS -> CS -> Prop :=
| ee_refl : forall s, exec_end s s
| ee_kernel_end : forall s s', runsToEnd cblock s s' -> exec_end s s'
| ee_final_fault : forall s s' s'',
                     priv s = false ->
                     cstep cblock s Silent s' ->
                     runsToEnd cblock s' s'' ->
                     exec_end s s''.
Hint Constructors exec_end.

Inductive cexec : CS -> ctrace -> CS -> Prop :=
| ce_end : forall s s', exec_end s s' -> cexec s nil s'
| ce_kernel_begin : forall s s' t s'',
                      runsUntilUser cblock s s' ->
                      cexec s' t s'' ->
                      cexec s t s''
| ce_user_hit : forall s e s' t s'',
                  priv s = false ->
                  cstep cblock s e s' ->
                  priv s' = false ->
                  cexec s' t s'' ->
                  cexec s (op_cons e t) s''
| ce_user_miss : forall s s' s'' t s''',
                   priv s = false ->
                   cstep cblock s Silent s' ->
                   runsUntilUser cblock s' s'' ->
                   cexec s'' t s''' ->
                   cexec s t s'''.
Hint Constructors cexec.

Lemma exec_end_step : forall s e s' s''
                             (STEP : cstep cblock s e s')
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
Hint Resolve exec_end_step.

Lemma cexec_step : forall s e s' t s''
                          (Hstep : cstep cblock s e s')
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
                     (@TINI.exec (concrete_machine cblock faultHandler)) s t s' ->
                     cexec s t s'.
Proof.
  intros s t s' Hexec.
  induction Hexec; eauto.
  - eapply cexec_step with (e := E e); eauto.
  - eapply cexec_step with (e := Silent); eauto.
Qed.

End CExec.

Lemma quasi_abstract_concrete_sref_prop :
  @state_refinement_statement (quasi_abstract_machine fetch_rule_g)
                              (concrete_machine cblock faultHandler)
                              match_states match_events.
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
    unfold match_events in *. subst.
    (*assert (exists t', t = filter (@is_event _) t') by
        (destruct (concretize_event e1); eauto using filter_cons_inv).*)
    (*inv H2.*)
    exploit IHEXEC; eauto.
    intros [t1 [? [? ?]]].
    exists (op_cons e1 t1). eexists.
    split. destruct e1; econstructor; eauto.

    simpl.
    inv ME; simpl; eauto.
    constructor; auto.
  - exploit cache_miss_simulation; eauto.
Qed.

Definition quasi_abstract_concrete_sref :=
  {| sref_prop := quasi_abstract_concrete_sref_prop |}.

Definition quasi_abstract_concrete_ref :
  refinement (quasi_abstract_machine fetch_rule_g)
             (concrete_machine cblock faultHandler) :=
  @refinement_from_state_refinement _ _
                                    quasi_abstract_concrete_sref
                                    ac_match_initial_data
                                    ac_match_initial_data_match_initial_states.

End RefQAC.

End Refinement.
