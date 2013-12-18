Require Import List.
Require Import ZArith.
Require Import FunctionalExtensionality.
Require Import Utils.
Require Import Lattices.
Require Import CLattices.
Require Import Instr.
Require Import AbstractCommon.
Require Import Rules.
Require Import AbstractMachine.
Require Import QuasiAbstractMachine.
Require Import Concrete.
Require Import ConcreteMachine.
Require Import ConcreteExecutions.
Require Import Determinism.
Require Import Refinement.
Require Import FaultRoutine.
Require Import Semantics.
Require Import Encodable.

Open Scope Z_scope.
Coercion Z_of_nat : nat >-> Z.

(** The Concrete Machine (with appropriate Fault Handler) refines the Abstract Machine. *)

Set Implicit Arguments.

(** * First refinement : from the abstract to the quasi-abstract machine *)
Section AbstractQuasiAbstract.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

Lemma abstract_step_equiv : forall s e s',
                              step tini_quasi_abstract_machine s e s' <->
                              step abstract_machine s e s'.
Proof.
  intros.
  split; intro H; inv H;
  unfold QuasiAbstractMachine.ifc_run_tmr, apply_rule in *;
  simpl in *;
  repeat match goal with
           | H : Some _ = Some _ |- _ =>
             inv H
           | H : (if ?b then _ else _) = _ |- _ =>
             destruct b eqn:E; inv H
         end;
  unfold Vector.nth_order in *; simpl in *;
  try econstructor (solve [compute; eauto]).

  econstructor; eauto.
  unfold QuasiAbstractMachine.ifc_run_tmr, apply_rule. simpl.
  unfold Vector.nth_order. simpl.
  rewrite CHECK. trivial.
Qed.

Program Definition abstract_quasi_abstract_sref :=
  @strong_refinement abstract_machine
                     tini_quasi_abstract_machine
                     eq eq _.
Next Obligation.
  exists a2. exists s22.
  repeat split; trivial.
  rewrite <- (abstract_step_equiv s21 a2 s22).
  auto.
  destruct a2; constructor; auto.
Qed.

Program Definition abstract_quasi_abstract_ref :=
  @refinement_from_state_refinement abstract_machine tini_quasi_abstract_machine
                                    abstract_quasi_abstract_sref eq
                                    _.

End AbstractQuasiAbstract.

(** * Second Refinement:
     from the quasi-abstract machine to the concrete machine *)

(** Matching relation between concrete and abstract values
    Generic in the rule table and fault handler *)
Section MatchAbstractConcrete.

Context {L: Type}
        {Latt: JoinSemiLattice L}
        {CLatt: ConcreteLattice L}
        {ELatt : Encodable L}
        {WFCLatt: WfConcreteLattice L Latt CLatt ELatt}.

Definition atom_labToZ (a:@Atom L) : (@Atom Z) :=
  let (v,l) := a in (v,labToZ l).

Definition atom_ZToLab (a:@Atom Z) : (@Atom L) :=
  let (v,l) := a in (v,ZToLab l).

Lemma atom_ZToLab_labToZ_id: forall (a:@Atom L), a = atom_ZToLab (atom_labToZ a).
Proof.
  intros. unfold atom_labToZ, atom_ZToLab. destruct a. f_equal.
  apply ZToLab_labToZ_id.
Qed.

Definition mem_labToZ (m: list (@Atom L)) : list (@Atom Z) :=
  map atom_labToZ m.

Definition mem_ZToLab (m: list (@Atom Z)) : list (@Atom L) :=
  map atom_ZToLab m.

Lemma mem_ZToLab_labToZ_id : forall (m: list (@Atom L)),
   m = mem_ZToLab (mem_labToZ m).
Proof.
  intros. unfold mem_ZToLab, mem_labToZ. rewrite map_map.
  replace (fun x => atom_ZToLab (atom_labToZ x)) with (@id (@Atom L)).
  rewrite map_id; auto.
  extensionality x.
  apply atom_ZToLab_labToZ_id.
Qed.

Lemma read_m_labToZ : forall m addrv xv xl,
 read_m addrv m = Some (xv, xl) ->
 read_m addrv (mem_labToZ m) = Some (xv, labToZ xl).
Proof.
  unfold read_m in *.
  destruct m ; intros.
  - case (addrv <? 0) in *. inv H.
    rewrite index_list_nil in H; inv H.
  - destruct addrv; simpl in *.
    + inv H. reflexivity.
    + edestruct (Pos2Nat.is_succ p0); eauto.
      rewrite H0 in *. simpl in *.
      unfold mem_labToZ. erewrite index_list_map; eauto.
      reflexivity.
    + inv H.
Qed.

Lemma read_m_labToZ' :
  forall i m xv xl,
    read_m i (mem_labToZ m) = Some (xv, xl) ->
    exists xl',
      read_m i m = Some (xv, xl') /\
      xl = labToZ xl'.
Proof.
  unfold index_list_Z.
  intros.
  destruct (i <? 0). inv H.
  gdep m.
  generalize (Z.to_nat i). clear i.
  intros i.
  induction i as [|i IH];
  intros m H;
  destruct m as [|[xv' xl'] m'];
  simpl in *; inv H; intuition.
  eexists. split; repeat f_equal.
Qed.

Lemma upd_m_labToZ : forall i xv xl m cm'
                            (UP : upd_m i (xv, labToZ xl) (mem_labToZ m) = Some cm'),
                       exists m',
                         upd_m i (xv, xl) m = Some m' /\
                         cm' = mem_labToZ m'.
Proof.
  intros i; unfold upd_m; intros.
  destruct (i <? 0). inv UP.
  gdep cm'. gdep m.
  generalize (Z.to_nat i). clear i.
  intros i.
  induction i as [|i IH];
  intros [| [xv' xl']] cm' UP; simpl in *; inv UP.
  repeat eexists.
  destruct (update_list i (xv, labToZ xl) (mem_labToZ l)) eqn:E; inv H0.
  guess tt IH.
  destruct IH. intuition.
  subst. eexists. rewrite H0.
  eauto.
Qed.

Inductive match_stacks : list (@StkElmt L) ->  list CStkElmt -> Prop :=
| ms_nil : match_stacks nil nil
| ms_cons_data: forall a ca s cs,
                  match_stacks s cs ->
                  ca = atom_labToZ a ->
                  match_stacks (AData a :: s) (CData ca :: cs)
| ms_cons_ret: forall a ca r s cs,
                  match_stacks s cs ->
                  ca = atom_labToZ a ->
                  match_stacks (ARet a r:: s) (CRet ca r false:: cs).
Hint Constructors match_stacks.

Lemma match_stacks_args :
  forall s args cs,
    match_stacks s (args ++ cs) ->
    exists args' s',
      s = args' ++ s' /\ match_stacks args' args /\ match_stacks s' cs.
Proof.
  intros s args. gdep s.
  induction args; intros.
  simpl in *. exists nil; exists s. split; auto.
  inv H;
    (exploit IHargs; eauto; intros [args' [cs' [Heq [Hmatch Hmatch']]]]);
    (inv Heq; (eexists; eexists; split; eauto ; try reflexivity)).
Qed.

Lemma match_stacks_length : forall s cs,
    match_stacks s cs ->
    length cs = length s.
Proof.
  induction 1; intros; (simpl; eauto).
Qed.

Lemma match_stacks_app : forall s cs s' cs',
    match_stacks s cs ->
    match_stacks s' cs' ->
    match_stacks (s++s') (cs++cs').
Proof.
  induction 1 ; intros; (simpl; eauto).
Qed.

Lemma match_stacks_data :
  forall s cs,
    match_stacks s cs ->
    (forall a : CStkElmt, In a cs -> exists d : Atom, a = CData d) ->
    (forall a : StkElmt, In a s -> exists d : Atom, a = AData d).
Proof.
  induction 1;  intros.
  - inv H0.
  - inv H2.  eauto.
    eapply IHmatch_stacks; eauto.
    intros; eapply H1; eauto.
    econstructor 2; eauto.
  - inv H2.
    eelim (H1 (CRet (atom_labToZ a) r false)); eauto. intros. inv H0.
    constructor; auto.
    eapply IHmatch_stacks; eauto.
    intros; eapply H1; eauto.
    econstructor 2; eauto.
Qed.

Lemma match_stacks_app_length : forall S CS,
    match_stacks S CS ->
    forall s s' cs cs',
    S = (s++s') ->
    CS = (cs++cs') ->
    length s = length cs ->
    match_stacks s cs
    /\ match_stacks s' cs'.
Proof.
  induction 1 ; intros; (simpl; eauto).
  - exploit app_eq_nil ; eauto. intros [Heq Heq']. inv Heq.
    exploit (app_eq_nil s) ; eauto. intros [Heq Heq']. inv Heq.
    split; eauto.
  - destruct s0 ; simpl in *. inv H1.
    destruct cs0 ; simpl in *. inv H2; split; eauto. congruence.
    inv H1. destruct cs0; simpl in *. congruence.
    inv H3.
    inv H2.
    exploit IHmatch_stacks; eauto.
    intros [Hmatch Hmatch']; split; eauto.
  - destruct s0 ; simpl in *. inv H1.
    destruct cs0 ; simpl in *. inv H2; split; eauto. congruence.
    inv H1. destruct cs0; simpl in *. congruence.
    inv H3.
    inv H2.
    exploit IHmatch_stacks; eauto.
    intros [Hmatch Hmatch']; split; eauto.
Qed.

Hint Constructors pop_to_return.

Lemma match_stacks_c_pop_to_return :
  forall astk cstk rpc rpcl b1 b2 cstk'
         (MATCH : match_stacks astk cstk)
         (POP : c_pop_to_return cstk (CRet (rpc, rpcl) b1 b2 :: cstk')),
    exists rpcl' astk',
      pop_to_return astk (ARet (rpc, rpcl') b1 :: astk') /\
      rpcl = labToZ rpcl' /\
      match_stacks astk' cstk'.
Proof.
  intros.
  gdep astk.
  match type of POP with
    | c_pop_to_return _ ?CSTK =>
      remember CSTK as cstk''
  end.
  induction POP; subst;
  intros astk MATCH; inv MATCH; try inv Heqcstk''; eauto;
  repeat match goal with
           | A : Atom |- _ => destruct A; simpl in *
           | H : (_, _) = (_, _) |- _ => inv H; simpl in *
         end;
  eauto.
  guess tt IHPOP.
  destruct IHPOP as [? [? [? [? ?]]]].
  subst. eauto 7.
Qed.
Hint Resolve match_stacks_c_pop_to_return.

(** Generic fault handler code *)
Variable fetch_rule_g : forall (o: OpCode), AllowModify (labelCount o).

Definition fetch_rule_impl : fetch_rule_impl_type :=
  fun o => existT _ (labelCount o) (fetch_rule_g o).

Definition LCL := LatticeConcreteLabels fetch_rule_impl.

Definition cache_up2date tmuc :=
  forall opcode vls pcl,
    cache_hit tmuc (opCodeToZ opcode) (labsToZs vls) (labToZ pcl) ->
    match apply_rule (fetch_rule_g opcode) pcl vls with
      | Some (rpcl,rl) => cache_hit_read tmuc (labToZ rl) (labToZ rpcl)
      | None => False
    end.

Definition cache_up2date_weak tmuc :=
  forall opcode vls pcl rl rpcl,
  forall (RULE: apply_rule (fetch_rule_g opcode) pcl vls = Some (rpcl, rl)),
  forall (CHIT: cache_hit tmuc (opCodeToZ opcode) (labsToZs vls) (labToZ pcl)),
         cache_hit_read tmuc (labToZ rl) (labToZ rpcl).

Lemma cache_up2date_success :
  forall tmuc, cache_up2date tmuc -> cache_up2date_weak tmuc.
Proof.
  unfold cache_up2date, cache_up2date_weak.
  intros.
  specialize (H opcode vls pcl CHIT).
  rewrite RULE in H.
  trivial.
Qed.

Definition faultHandler := @FaultRoutine.faultHandler L ELatt labelCount
                                                      (ifc_run_tmr fetch_rule_g)
                                                      LCL.

Inductive match_states : @AS L -> CS -> Prop :=
 ms: forall am cm i astk tmuc cstk apc cpc
              (CACHE: cache_up2date tmuc)
              (STKS: match_stacks astk cstk)
              (MEM: cm = mem_labToZ am)
              (PC: cpc = atom_labToZ apc),
         match_states (AState am i astk apc)
                      (CState tmuc cm faultHandler i cstk cpc false).

Lemma opCodeToZ_inj: forall o1 o2, opCodeToZ o1 = opCodeToZ o2 -> o1 = o2.
Proof.
  intros o1 o2 Heq.
  destruct o1, o2; inv Heq; try congruence.
Qed.

Lemma labsToZs_cons_hd: forall n0 a v0 b v3,
  S n0 <= 3 ->
  labsToZs (Vector.cons L a n0 v0) = labsToZs (Vector.cons L b n0 v3) ->
  a = b.
Proof.
  intros.  inv H0.
  unfold nth_labToZ in H2. destruct (le_lt_dec (S n0) 0).  inv l.
  unfold Vector.nth_order in H2. simpl in H2.
  apply labToZ_inj in H2.  auto.
Qed.

Lemma nth_labToZ_cons:
  forall nth n a v,
    nth_labToZ (Vector.cons L a n v) (S nth) = nth_labToZ v nth.
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
    labsToZs (Vector.cons L a n0 v0) = labsToZs (Vector.cons L b n0 v3) ->
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


Lemma labsToZs_inj: forall n (v1 v2: Vector.t L n), n <= 3 ->
     labsToZs v1 = labsToZs v2 -> v1 = v2.
Proof.
  intros n v1 v2.
  set (P:= fun n (v1 v2: Vector.t L n) => n <= 3 -> labsToZs v1 = labsToZs v2 -> v1 = v2) in *.
  eapply Vector.rect2 with (P0:= P); eauto.
  unfold P. auto.
  intros.
  unfold P in *. intros.
  exploit labsToZs_cons_hd; eauto. intros Heq ; inv Heq.
  eapply labsToZs_cons_tail in H1; eauto.
  exploit H ; eauto. zify; omega.
  intros Heq. inv Heq.
  reflexivity. zify ; omega.
Qed.

Definition abstract_action (ce : CEvent+τ) : (@Event L)+τ :=
  match ce with
    | E (CEInt ca) => E (EInt (atom_ZToLab ca))
    | Silent => Silent
  end.

Definition concretize_action (ae : (@Event L)+τ) : CEvent+τ :=
  match ae with
    | E (EInt aa) => E (CEInt (atom_labToZ aa))
    | Silent => Silent
  end.

Definition match_actions a1 a2 := concretize_action a1 = a2.

Lemma abstract_action_concretize_action :
  forall ae, abstract_action (concretize_action ae) = ae.
Proof.
  intros [[[xv xl]]|]; simpl; auto.
  rewrite <- ZToLab_labToZ_id.
  reflexivity.
Qed.


(** The refinement proof itself. Generic in the rule table used to generate the fault handler *)

Section RefQAC.

(* Reconstruct the quasi_abstract label vector *)
Ltac quasi_abstract_labels :=
  match goal with
    | L : Type,
      Latt : JoinSemiLattice ?L,
      H : context[cache_hit _ _ (dontCare, dontCare, dontCare) _] |- _ =>
      pose (vls := Vector.nil L)
    | H : context[cache_hit _ _ (labToZ ?l, dontCare, dontCare) _] |- _ =>
      pose (vls := Vector.cons _ l _ (Vector.nil _))
    | H : context[cache_hit _ _ (labToZ ?l1, labToZ ?l2, dontCare) _] |- _ =>
      pose (vls := Vector.cons _ l1 _ (Vector.cons _ l2 _ (Vector.nil _)))
    | H : context[cache_hit _ _ (labToZ ?l1, labToZ ?l2, labToZ ?l3) _] |- _ =>
      pose (vls := Vector.cons _ l1 _
                               (Vector.cons _ l2 _
                                            (Vector.cons _ l3 _ (Vector.nil _))))
  end.

(* Relate the results of a cache read to its arguments *)
Ltac analyze_cache_hit OP vls apcl:=
  match goal with
    | CACHE : cache_up2date _ |- _ =>
      let H := fresh "H" in
      generalize (@CACHE OP vls apcl);
      intros H; guess tt H;
      try match type of H with
        | context[ (apply_rule (fetch_rule_g ?r) ?aapcl ?vvls) ] =>
          destruct (apply_rule (fetch_rule_g r) aapcl vvls) as [[? ?]|] eqn:Happly ;
            [| inv H]
      end
  end;
  match goal with
    | H1 : cache_hit_read _ _ _,
      H2 : cache_hit_read _ _ _ |- _ =>
      let H := fresh "H" in
      generalize (cache_hit_read_determ H2 H1);
        intros H;
        destruct H;
        subst;
        clear H2
      end.

(** Cache hit case *)

Lemma cache_hit_simulation :
  forall s1 s2 e2 s2'
         (Hmatch : match_states s1 s2)
         (Hs2' : priv s2' = false)
         (Hstep : cstep s2 e2 s2'),
    exists a1 s1', step_rules (ifc_run_tmr fetch_rule_g) s1 a1 s1' /\
                   match_actions a1 e2 /\
                   match_states s1' s2'.
Proof.
  intros.
  inv Hmatch.
  unfold match_actions.
  destruct apc as [apc apcl].
  inv Hstep; simpl in *; try congruence;

  (* Invert some hypotheses *)
  repeat match goal with
           | H : ?x = ?x |- _ => clear H
           | H : match_stacks _ (_ ::: _) |- _ => inv H
           | H : match_stacks _ (_ ++ _) |- _ =>
             apply match_stacks_args' in H;
             destruct H as [? [? [? [? ?]]]];
             subst
           | a : _,
             H : (_, _) = atom_labToZ ?a |- _ =>
             destruct a; simpl in H; inv H
         end;

  (* For the Load/Store cases *)
  try_exploit read_m_labToZ';

  (* For the Ret cases *)
  try_exploit match_stacks_c_pop_to_return;

  quasi_abstract_labels;

  (* Find the current opcode *)
  match goal with
    | H : read_m _ _ = Some ?instr |- _ =>
      let opcode := (eval compute in (opcode_of_instr instr)) in
      match opcode with
        | Some ?opcode => pose (OP := opcode)
      end
  end;

  analyze_cache_hit OP vls apcl;

  subst OP vls;

  (* For the Store case *)
  try_exploit upd_m_labToZ;

  (* For the BranchNZ case *)
  try match goal with
        | |- context[if (?z =? 0) then _ else _ ] =>
          let H := fresh "H" in
          assert (H := Z.eqb_spec z 0);
          destruct (z =? 0);
          inv H
      end;

  try solve [
        eexists; eexists; split; try split;
        try (econstructor (solve [compute; eauto]));
        repeat (constructor; eauto); simpl; f_equal; intuition
      ].

  - exists Silent.
    exploit match_stacks_args; eauto. intros [args' [s' [Hargs' [Hmatchargs' Hmatchs']]]].
    subst. eexists. split.

    + eapply (step_call (ifc_run_tmr fetch_rule_g)); try solve [compute; eauto].
      * symmetry. eapply match_stacks_length; eauto.
      * eapply match_stacks_data; eauto.

    + repeat (constructor; eauto); simpl; f_equal; intuition.
      eauto using match_stacks_app.
Qed.

(** Cache miss case *)

Lemma invalid_pc_no_step :
  forall s1 e s2
         (STEP : cstep s1 e s2)
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
         (RUN1 : runsUntilUser s1 s21)
         (RUN2 : runsToEnd s1 s22)
         (FAIL : fst (pc s22) < 0),
    False.
Proof.
  intros.
  induction RUN1; inv RUN2;
  try match goal with
        | [ H1 : cstep ?s _ _,
            H2 : cstep ?s _ _
            |- _ ] =>
          let H := fresh "H" in
          generalize (cmach_determ H1 H2);
          intros [? ?]; subst
      end; eauto;
  try match goal with
        | [ H : runsUntilUser _ _ |- _ ] =>
          generalize (runsUntilUser_l H);
          intros
      end;
  try match goal with
        | [ H : runsToEnd _ _ |- _ ] =>
          generalize (runsToEnd_l H);
          intros
      end;
  try congruence;
  eauto using invalid_pc_no_step ; eauto.
Qed.

Lemma kernel_fail_determ :
  forall s1 s21 s22
         (RUN1 : runsToEnd s1 s21)
         (FAIL1 : fst (pc s21) < 0)
         (RUN2 : runsToEnd s1 s22)
         (FAIL2 : fst (pc s22) < 0),
    s21 = s22.
Proof.
  intros.
  induction RUN1; inv RUN2; trivial;
  try solve [exfalso; eauto using invalid_pc_no_step];
  try match goal with
        | [ H1 : cstep ?s _ _,
            H2 : cstep ?s _ _
            |- _ ] =>
          let H := fresh "H" in
          generalize (cmach_determ H1 H2);
          intros [? ?]; subst
      end; eauto.
Qed.

Lemma runsToEscape_determ :
  forall s1 s21 s22
         (RUN1 : runsToEscape s1 s21)
         (RUN2 : runsToEscape s1 s22),
    s21 = s22.
Proof.
  intros.
  inv RUN1; inv RUN2;
  eauto using runsUntilUser_determ,
              kernel_fail_determ;
  try solve [exfalso; eauto using kernel_run_success_fail_contra];
  try match goal with
        | [ H : runsUntilUser _ _ |- _ ] =>
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

Lemma configuration_at_miss :
  forall s1 s21 e2 s22
         (MATCH : match_states s1 s21)
         (STEP : cstep s21 e2 s22)
         (PRIV : priv s22 = true),
    exists opcode (vls : Vector.t L (projT1 (fetch_rule_impl opcode))),
      cache_hit (cache s22) (opCodeToZ opcode)
                (labsToZs vls) (labToZ (snd (apc s1))) /\
      mem s22 = mem s21 /\
      fhdl s22 = fhdl s21 /\
      imem s22 = imem s21 /\
      stk s22 = CRet (pc s21) false false :: stk s21 /\
      pc s22 = (0, handlerTag).
Proof.
  intros.
  inv MATCH.
  inv STEP; simpl in *; try congruence;

  (* Invert some hypotheses *)
  repeat match goal with
           | H : true = false |- _ => inv H
           | H : ?x = ?x |- _ => clear H
           | H : match_stacks _ (_ ::: _) |- _ => inv H
           | H : match_stacks _ (_ ++ _) |- _ =>
             apply match_stacks_args' in H;
             destruct H as [? [? [? [? ?]]]];
             subst
           | a : _,
             H : (_, _) = atom_labToZ ?a |- _ =>
             destruct a; simpl in H; inv H
         end;

    (* For the Load case *)
  try_exploit read_m_labToZ';

  (* For the Ret cases *)
  try_exploit match_stacks_c_pop_to_return;

  try quasi_abstract_labels;

  match goal with
    | H : read_m _ _ = Some ?i |- _ =>
      let oc := eval compute in (opcode_of_instr i) in
      match oc with
        | Some ?oc => (exists oc)
      end
  end;

  exists vls; repeat econstructor;
  unfold update_cache;
  rewrite index_list_Z_update_list_list; eauto;
  compute; reflexivity.
Qed.

Lemma update_cache_spec_rvec_cache_hit :
  forall rpcl rl cache cache' op tags pc
         (MATCH : handler_final_mem_matches rpcl rl cache cache')
         (HIT : cache_hit cache op tags pc),
    cache_hit cache' op tags pc.
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
  destruct RES.
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
  intros. inv CHIT; inv CHIT'.
  inv OP; inv OP0.
  inv TAG1; inv TAG0.
  inv TAG2; inv TAG4.
  inv TAG3; inv TAG5.
  inv TAGPC; inv TAGPC0.
  repeat allinv'.
  intuition.
Qed.

Lemma cache_miss_simulation :
  forall s1 s21 e21 s22 s23
         (MATCH : match_states s1 s21)
         (STEP1 : cstep s21 e21 s22)
         (RUN : runsUntilUser s22 s23),
    match_states s1 s23.
Proof.
  intros.
  exploit runsUntilUser_l; eauto.
  intros PRIV.
  exploit configuration_at_miss; eauto.
  intros [op [vls [HIT EQS]]].
  destruct s22; simpl in EQS, PRIV; subst.
  inv MATCH; simpl.
  intuition. subst.
  destruct (apply_rule (projT2 (fetch_rule_impl op)) (snd apc) vls)
    as [[orl rpcl]|] eqn:E.
  - exploit (handler_correct_succeed (CT := LCL)); eauto.
    intros [cache' [ESCAPE1 MATCH']].
    exploit rte_success; eauto.
    intros ESCAPE2.
    unfold faultHandler in *.
    generalize (runsToEscape_determ ESCAPE1 ESCAPE2).
    intros H. subst.
    constructor; eauto.
    simpl in *.
    exploit update_cache_spec_rvec_cache_hit; eauto.
    clear HIT. intros HIT.
    intros op' vls' pcl' HIT'.
    generalize (cache_hit_unique HIT HIT').
    intros [E1 [E2 E3]].
    apply opCodeToZ_inj in E1. subst.
    apply labToZ_inj in E3. subst.
    apply labsToZs_inj in E2.
    + subst. rewrite E.
      destruct MATCH'. trivial.
    + destruct op'; simpl; omega.
  - exploit (handler_correct_fail (CT := LCL)); eauto.
    simpl in *.
    intros [stk' ESCAPE1].
    inv ESCAPE1.
    + apply runsUntilUser_r in STAR. simpl in STAR. congruence.
    + exfalso.
      eapply kernel_run_success_fail_contra; eauto.
Qed.

Lemma filter_cons_inv :
  forall A (f : A -> bool) a l1 l2,
    a :: l1 = filter f l2 ->
    exists l2', l1 = filter f l2'.
Proof.
  induction l2 as [|a' l2 IH]; simpl. congruence.
  destruct (f a'); intros H; auto.
  inv H. eauto.
Qed.

Inductive ac_match_initial_data :
  init_data abstract_machine ->
  init_data (concrete_machine faultHandler) -> Prop :=
| ac_mid : forall d1 p1 n1 b1,
             ac_match_initial_data
               (p1, d1, n1, b1)
               (p1, mem_labToZ d1, n1, labToZ b1).

Lemma match_init_stacks: forall d1,
 match_stacks (map (fun a : Atom => AData a) d1)
     (map (fun a : Atom => CData a) (mem_labToZ d1)).
Proof.
  induction d1 ; intros;
  (simpl ; constructor; auto).
Qed.

Lemma replicate_mem_labToZ :
  forall b n,
    replicate (0, labToZ b) n = mem_labToZ (replicate (0, b) n).
Proof.
  induction n ; intros.
  auto.
  simpl. inv IHn. auto.
Qed.

Lemma ac_match_initial_data_match_initial_states :
  forall ai ci,
    ac_match_initial_data ai ci ->
    match_states (init_state abstract_machine ai)
                      (init_state (concrete_machine faultHandler) ci).
Proof.
  intros ai ci H. inv H.
  simpl in *.
  constructor; simpl; eauto.
  - intros op vls pcl contra.
    inv contra.
    destruct op;
    destruct OP as [OP]; inv OP.
  - apply match_init_stacks.
  - apply replicate_mem_labToZ.
Qed.

(** Notions of concrete executions for proving this refinement *)
Section CExec.

(* congruence fails if this is let-bound *)
Local Notation ctrace := (list CEvent).

Let cons_event e t : ctrace :=
  match e with
    | E e => e :: t
    | Silent => t
  end.

Inductive exec_end : CS -> CS -> Prop :=
| ee_refl : forall s, exec_end s s
| ee_kernel_end : forall s s', runsToEnd s s' -> exec_end s s'
| ee_final_fault : forall s s' s'',
                     priv s = false ->
                     cstep s Silent s' ->
                     runsToEnd s' s'' ->
                     exec_end s s''.
Hint Constructors exec_end.

Inductive cexec : CS -> ctrace -> CS -> Prop :=
| ce_end : forall s s', exec_end s s' -> cexec s nil s'
| ce_kernel_begin : forall s s' t s'',
                      runsUntilUser s s' ->
                      cexec s' t s'' ->
                      cexec s t s''
| ce_user_hit : forall s e s' t s'',
                  priv s = false ->
                  cstep s e s' ->
                  priv s' = false ->
                  cexec s' t s'' ->
                  cexec s (cons_event e t) s''
| ce_user_miss : forall s s' s'' t s''',
                   priv s = false ->
                   cstep s Silent s' ->
                   runsUntilUser s' s'' ->
                   cexec s'' t s''' ->
                   cexec s t s'''.
Hint Constructors cexec.

Lemma exec_end_step : forall s e s' s''
                             (STEP : cstep s e s')
                             (EXEC : exec_end s' s''),
                        cexec s (cons_event e nil) s''.
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
                          (Hstep : cstep s e s')
                          (Hexec : cexec s' t s''),
                          cexec s (cons_event e t) s''.
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

Definition is_E {T} (a:T+τ) : bool :=
  match a with
    | Silent => false
    | E _ => true
  end.

Lemma exec_cexec : forall s t s',
                     (@TINI.exec (concrete_machine faultHandler)) s t s' ->
                     cexec s t s'.
Proof.
  intros s t s' Hexec.
  induction Hexec; eauto.
  eapply cexec_step with (e:=E e); eauto.
  eapply cexec_step with (e:=Silent); eauto.
Qed.

End CExec.

Definition match_events (e1:@Event L) (e2:CEvent) : Prop :=
  match e1 with
      EInt aa => CEInt (atom_labToZ aa) = e2
  end.

Lemma quasi_abstract_concrete_sref_prop :
  @state_refinement_statement (ifc_quasi_abstract_machine fetch_rule_g)
                              (concrete_machine faultHandler)
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
    unfold match_actions in *. subst.
    exploit IHEXEC; eauto.
    intros [t1 [? [? ?]]].
    destruct e1; simpl.
    + exists (e::t1). eexists.
      split. econstructor 2; eauto.
      simpl. destruct e; simpl; eauto.
      constructor; auto.
      constructor; auto.
    + exists (t1). eexists.
      split. econstructor; eauto.
      auto.

  - exploit cache_miss_simulation; eauto.
Qed.

Definition quasi_abstract_concrete_sref :=
  {| sref_prop := quasi_abstract_concrete_sref_prop |}.

Definition quasi_abstract_concrete_ref :
  refinement (ifc_quasi_abstract_machine fetch_rule_g)
             (concrete_machine faultHandler) :=
  @refinement_from_state_refinement _ _
                                    quasi_abstract_concrete_sref
                                    ac_match_initial_data
                                    ac_match_initial_data_match_initial_states.


End RefQAC.
End MatchAbstractConcrete.

(** * Combining the above into the final result *)
(** This is where we instantiate the generic refinement. *)
Section RefAC.

Context {observer: Type}
        {Latt: JoinSemiLattice observer}
        {CLatt: ConcreteLattice observer}
        {ELatt : Encodable observer}
        {WFCLatt: WfConcreteLattice observer Latt CLatt ELatt}.

Definition tini_fetch_rule_withsig :=
  (fun opcode => existT _
                        (QuasiAbstractMachine.labelCount opcode)
                        (QuasiAbstractMachine.fetch_rule opcode)).
Definition tini_faultHandler := @FaultRoutine.faultHandler observer ELatt
                                                           labelCount
                                                           (ifc_run_tmr fetch_rule)
                                                           (LatticeConcreteLabels (fetch_rule_impl fetch_rule)).
Definition tini_match_states := match_states QuasiAbstractMachine.fetch_rule.

Definition tini_concrete_machine := concrete_machine tini_faultHandler.

Program Definition abstract_concrete_ref :
  refinement abstract_machine tini_concrete_machine :=
  @ref_composition _ _ _
                   abstract_quasi_abstract_ref
                   (quasi_abstract_concrete_ref fetch_rule)
                   (@ac_match_initial_data _ _ _ _ _ fetch_rule)
                   match_events
                   _ _.

Next Obligation.
  eauto.
Qed.

End RefAC.
