Require Import List.
Require Import ZArith.
Require Import FunctionalExtensionality.

Require Import Utils.
Require Import Lattices.
Require Import CLattices.
Require Import Instr.
Require Import CodeTriples.
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

Open Scope Z_scope.
Coercion Z_of_nat : nat >-> Z.

Set Implicit Arguments.

(** * First refinement : from the abstract to the quasi-abstract machine *)
Section AbstractQuasiAbstract.

Context {T: Type}
        {Latt: JoinSemiLattice T}.
Variable SysTable: syscall_table T.

Lemma abstract_step_equiv : forall s e s',
  step (tini_quasi_abstract_machine SysTable) s e s' <->
  step (abstract_machine SysTable) s e s'.
Proof.
  intros.
  split; intro H; inv H;
  unfold QuasiAbstractMachine.run_tmr, apply_rule in *;
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
  unfold QuasiAbstractMachine.run_tmr, apply_rule. simpl.
  unfold Vector.nth_order. simpl.
  rewrite CHECK. trivial.
Qed.

Program Definition abstract_quasi_abstract_sref :=
  @strong_refinement (abstract_machine SysTable)
                     (tini_quasi_abstract_machine SysTable)
                     eq eq _.
Next Obligation.
  exists e2. exists s22.
  repeat split; trivial.
  rewrite <- (abstract_step_equiv s21 e2 s22).
  auto.
  destruct e2; constructor; auto.
Qed.

Program Definition abstract_quasi_abstract_ref :=
  @refinement_from_state_refinement (abstract_machine SysTable)
                                    (tini_quasi_abstract_machine SysTable)
                                    abstract_quasi_abstract_sref eq
                                    _.

End AbstractQuasiAbstract.

(** * Second Refinement:
     from the QUASI_ABSTRACT_MACHINE to the concrete machine *)

(** Matching relation between concrete and abstract values
    Generic in the rule table and fault handler *)
Section MatchAbstractConcrete.

Variable fetch_rule_g : forall (o: OpCode), AllowModify (labelCount o).

Definition fetch_rule_impl : fetch_rule_impl_type :=
  fun o => existT _ (labelCount o) (fetch_rule_g o).

(** This part of the proof that can be done generically, i.e not having to deal with the init_data
problem (we prove only the state refinement)  *)
Section StateRefinement.

Context {L: Type}
        {Latt: JoinSemiLattice L}
        {CLatt: ConcreteLattice L}
        {SysTable: syscall_table L}
        {WFCLatt: WfConcreteLattice L Latt CLatt SysTable}.

Inductive match_atoms (m : list (@Atom Z)) : @Atom L -> @Atom Z -> Prop :=
| al2z : forall z l t
                (TAG : labToZ l t m),
           match_atoms m (z, l) (z, t).
Hint Constructors match_atoms.

Definition atom_ZToLab (a:@Atom Z) m : (@Atom L) :=
  let (v,t) := a in (v,ZToLab t m).

Lemma atom_labToZ_ZToLab_id : forall aa ca m,
                                match_atoms m aa ca ->
                                atom_ZToLab ca m = aa.
Proof.
  intros.
  inv H.
  simpl.
  apply labToZ_ZToLab_id in TAG.
  rewrite TAG.
  reflexivity.
Qed.

Definition match_memories m := Forall2 (match_atoms m).
Hint Unfold match_memories.
Hint Constructors Forall2.

(*
Definition mem_ZToLab cm m :=
  map (fun ca => atom_ZToLab ca m) cm.

Lemma mem_ZToLab_labToZ_id : forall am cm m,
                               mem_labToZ am cm m ->
                               mem_ZToLab cm m = am.
Proof.
  intros. unfold mem_ZToLab, mem_labToZ in *.
  induction H as [|aa ca am cm ATOMS MEMS IH]; auto.
  simpl.
  rewrite IH. f_equal.
  apply atom_labToZ_ZToLab_id.
  assumption.
Qed.
*)

Lemma read_m_labToZ :
  forall i am cm c ac
         (MEMS : match_memories c am cm)
         (READ : read_m i cm = Some ac),
  exists aa,
    read_m i am = Some aa /\
    match_atoms c aa ac.
Proof.
  unfold index_list_Z.
  intros.
  destruct (i <? 0). inv READ.
  gdep (Z.to_nat i). clear i.
  induction MEMS as [|aa' ac' am cm ATOMS MEMS IH];
  intros [|i] READ; simpl in *; try congruence.
  - inv READ. eauto.
  - exploit IH; eauto.
Qed.

Lemma upd_m_labToZ : forall i am cm c aa ac cm'
                            (MEMS : match_memories c am cm)
                            (ATOMS : match_atoms c aa ac)
                            (UP : upd_m i ac cm = Some cm'),
                     exists am',
                       upd_m i aa am = Some am' /\
                       match_memories c am' cm'.
Proof.
  intros i; unfold upd_m; intros.
  destruct (i <? 0). inv UP.
  gdep cm'. gdep (Z.to_nat i). clear i.
  induction MEMS as [|aa' ac' am cm ATOMS' MEMS IH]; intros [|i] cm' UP;
  simpl in *; try congruence.
  - inv UP. eauto.
  - destruct (update_list i ac cm) as [am'|] eqn:UP'; try congruence.
    inv UP.
    exploit IH; eauto.
    intros [am'' [H1 H2]].
    rewrite H1.
    eauto.
Qed.

Inductive match_stk_elmt (m : list (@Atom Z)): @StkElmt L -> CStkElmt -> Prop :=
| mse_data : forall a1 a2
                    (ATOMS : match_atoms m a1 a2),
               match_stk_elmt m (AData a1) (CData a2)
| mse_ret : forall pc1 pc2 b
                   (ATOMS : match_atoms m pc1 pc2),
              match_stk_elmt m (ARet pc1 b) (CRet pc2 b false).
Hint Constructors match_stk_elmt.

Definition match_stacks m := Forall2 (match_stk_elmt m).
Hint Unfold match_stacks.

Lemma match_stacks_args :
  forall s args cs m,
    match_stacks m s (args ++ cs) ->
    exists args' s',
      s = args' ++ s' /\ match_stacks m args' args /\ match_stacks m s' cs.
Proof.
  intros.
  apply Forall2_app_inv_r in H.
  destruct H as [? [? [? [? ?]]]]. eauto.
Qed.

Lemma match_stacks_length : forall m s cs,
    match_stacks m s cs ->
    length s = length cs.
Proof.
  induction 1; intros; (simpl; eauto).
Qed.
Hint Resolve match_stacks_length.

Lemma match_stacks_app : forall s cs s' cs' m,
    match_stacks m s cs ->
    match_stacks m s' cs' ->
    match_stacks m (s++s') (cs++cs').
Proof.
  eauto using Forall2_app.
Qed.
Hint Resolve match_stacks_app.

Lemma match_stacks_data :
  forall s cs m,
    match_stacks m s cs ->
    (forall a : CStkElmt, In a cs -> exists d : Atom, a = CData d) ->
    (forall a : StkElmt, In a s -> exists d : Atom, a = AData d).
Proof.
  induction 1;  intros.
  - inv H0.
  - inv H2.
    + inv H; eauto.
      eelim (H1 (CRet pc2 b false)); simpl; eauto; try congruence.
    + apply IHForall2; simpl in *; eauto.
Qed.

Lemma match_stacks_app_length : forall S CS m,
    match_stacks m S CS ->
    forall s s' cs cs',
    S = (s++s') ->
    CS = (cs++cs') ->
    length s = length cs ->
    match_stacks m s cs
    /\ match_stacks m s' cs'.
Proof.
  intros. subst. gdep cs.
  induction s as [|se s IH]; intros; destruct cs as [|cse cs]; simpl in *;
  inv H2; eauto.
  inv H.
  exploit IH; eauto.
  intuition.
Qed.

Hint Constructors pop_to_return.

Lemma match_stacks_c_pop_to_return :
  forall astk cstk rpc rpcl b1 b2 cstk' m
         (MATCH : match_stacks m astk cstk)
         (POP : c_pop_to_return cstk (CRet (rpc, rpcl) b1 b2 :: cstk')),
    exists rpcl' astk',
      pop_to_return astk (ARet (rpc, rpcl') b1 :: astk') /\
      labToZ rpcl' rpcl m /\
      match_stacks m astk' cstk'.
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
           | H : match_stk_elmt _ _ _ |- _ => inv H
           | H : match_atoms _ _ _ |- _ => inv H
         end; eauto.
  guess tt IHPOP.
  destruct IHPOP as [? [? [? [? ?]]]].
  subst. eauto 7.
Qed.
Hint Resolve match_stacks_c_pop_to_return.

(** Generic fault handler code *)

Definition cache_up2date tmuc :=
  forall opcode ts pct,
    cache_hit tmuc (opCodeToZ opcode) ts pct ->
    exists vls pcl rpcl rpct rl rt,
      labsToZs vls tmuc ts /\
      labToZ pcl pct tmuc /\
      labToZ rpcl rpct tmuc /\
      labToZ rl rt tmuc /\
      apply_rule (fetch_rule_g opcode) pcl vls = Some (rpcl, rl) /\
      cache_hit_read tmuc rt rpct.

Definition faultHandler := FaultRoutine.faultHandler fetch_rule_impl.
Variable syscall_code : list Instr.
Definition kernel_code := faultHandler++syscall_code.

Definition well_placed_syscall_implem {T} (sys_info:@syscall_info T) (kc:list Instr) : Prop :=
  CodeTriples.code_at (si_pc sys_info) kc (si_instrs sys_info).  

Definition wf_systable (kc:list Instr) : Prop :=
  forall id sys_info, 
    SysTable id = Some sys_info -> 
    well_placed_syscall_implem sys_info kc.

Inductive match_states : @AS L -> CS -> Prop :=
 ms: forall am cm i astk tmuc cstk apc cpc
              (CACHE: cache_up2date tmuc)
              (CACHEDEF: mem_def_on_cache tmuc)
              (STKS: match_stacks tmuc astk cstk)
              (MEM: match_memories tmuc am cm)
              (PC: match_atoms tmuc apc cpc)
              (WFST: wf_systable kernel_code),
         match_states (AState am i astk apc)
                      (CState tmuc cm kernel_code i cstk cpc false).

Lemma opCodeToZ_inj: forall o1 o2, opCodeToZ o1 = opCodeToZ o2 -> o1 = o2.
Proof.
  intros o1 o2 Heq.
  destruct o1, o2; inv Heq; try congruence.
Qed.

Lemma labsToZs_cons_hd: forall n0 a v0 b v3 m ts,
  S n0 <= 3 ->
  labsToZs (Vector.cons L a n0 v0) m ts ->
  labsToZs (Vector.cons L b n0 v3) m ts ->
  a = b.
Proof.
  unfold labsToZs.
  destruct ts as ((z0 & z1) & z2).
  intuition.
  unfold nth_labToZ in H2. destruct (le_lt_dec (S n0) 0).  inv l.
  unfold Vector.nth_order in H2. simpl in H2.
  unfold nth_labToZ in H0. destruct (le_lt_dec (S n0) 0).  inv l0.
  unfold Vector.nth_order in H0. simpl in H0.
  eapply labToZ_inj; eauto.
Qed.

Lemma nth_labToZ_cons:
  forall nth n a v m ts,
    nth_labToZ (Vector.cons L a n v) (S nth) m ts ->
    nth_labToZ v nth m ts.
Proof.
  induction n; simpl; intros.
  - unfold nth_labToZ in *.
    case_eq (le_lt_dec (S nth) 1); case_eq (le_lt_dec nth 0); intros; auto;
    try (zify ; omega).
  - unfold nth_labToZ in *.
    destruct (le_lt_dec (S (S n)) (S nth)) eqn:E; case_eq (le_lt_dec (S n) nth); intros; auto;
    try (zify ; omega).
    unfold Vector.nth_order in *. simpl in H.
    erewrite of_nat_lt_proof_irrel ; eauto.
Qed.

Lemma labsToZs_cons_tail:
  forall n0 a v0 b v3 ts m,
    (n0 <= 2)%nat ->
    labsToZs (Vector.cons L a n0 v0) m ts ->
    labsToZs (Vector.cons L b n0 v3) m ts ->
    exists ts',
      labsToZs v0 m ts' /\  labsToZs v3 m ts'.
Proof.
  intros.
   unfold labsToZs in *.
  destruct ts as ((z0 & z1) & z2).
  destruct H0 as (T1 & T2 & T3).
  destruct H1 as (U1 & U2 & U3).
  exists (z1,z2,dontCare); repeat split;
  try (eapply nth_labToZ_cons; eauto; fail).
  unfold nth_labToZ.
  destruct (le_lt_dec n0 2); auto; zify ; omega.
  unfold nth_labToZ.
  destruct (le_lt_dec n0 2); auto; zify ; omega.
Qed.


Lemma labsToZs_inj: forall n (v1 v2: Vector.t L n), n <= 3 ->
     forall ts m,
     labsToZs v1 m ts -> labsToZs v2 m ts -> v1 = v2.
Proof.
  intros n v1 v2.
  set (P:= fun n (v1 v2: Vector.t L n) => n <= 3 -> forall ts m,
                                                 labsToZs v1 m ts -> labsToZs v2 m ts -> v1 = v2) in *.
  apply Vector.rect2 with (P0:=P); unfold P; eauto.
  intros n0 v0 v3 H a b H0 ts m H1 H2.
  assert (a=b) by (eapply labsToZs_cons_hd; eauto).
  subst.
  f_equal.
  elim labsToZs_cons_tail with (2:=H1) (3:=H2).
  intros ts' (T1 & T2).
  apply H with ts' m; auto.
  zify; omega.
  zify; omega.
Qed.

Lemma cache_up2date_res :
  forall tmuc opcode vls ts pcl pct
         (UP2DATE : cache_up2date tmuc)
         (Hvls : labsToZs vls tmuc ts)
         (Hpc : labToZ pcl pct tmuc)
         (HIT : cache_hit tmuc (opCodeToZ opcode) ts pct),
    exists rpcl rpct rl rt,
      labToZ rpcl rpct tmuc /\
      labToZ rl rt tmuc /\
      apply_rule (fetch_rule_g opcode) pcl vls = Some (rpcl, rl) /\
      cache_hit_read tmuc rt rpct.
Proof.
  intros.
  apply UP2DATE in HIT.
  destruct HIT as [vls' [pcl' [rpcl [rpct [rl [rt H]]]]]].
  intuition.
  exists rpcl. exists rpct. exists rl. exists rt.
  repeat (split; auto).
  cut (vls' = vls /\ pcl' = pcl).
  { intros [E1 E2]. subst. assumption. }
  split.
  - eapply labsToZs_inj; eauto.
    destruct opcode; simpl; omega.
  - eapply labToZ_inj; eauto.
Qed.

Definition abstract_event (ce : CEvent+τ) : (@Event L)+τ :=
  match ce with
    | E (CEInt ca m) => E (EInt (atom_ZToLab ca m))
    | Silent => Silent
  end.

Inductive match_actions : (@Event L)+τ -> CEvent+τ -> Prop :=
| ma_not_silent : forall aa ca m
                         (ATOMS : match_atoms m aa ca),
                    match_actions (E (EInt aa)) (E (CEInt ca m))
| ma_silent : match_actions Silent Silent.
Hint Constructors match_actions.

(** The refinement proof itself. Generic in the rule table used to generate the FH *)

Section RefQAC.

Lemma analyze_cache_hit :
  forall m opcode (vls : Vector.t L (labelCount opcode)) ts pcl pct zrl zrpcl
         (LABS : labsToZs vls m ts)
         (PC : labToZ pcl pct m)
         (UP2DATE : cache_up2date m)
         (CHIT : cache_hit m (opCodeToZ opcode) ts pct)
         (CREAD : cache_hit_read m zrl zrpcl),
  exists rpcl rl,
    labToZ rl zrl m /\
    labToZ rpcl zrpcl m /\
    apply_rule (fetch_rule_g opcode) pcl vls = Some (rpcl, rl).
Proof.
  intros.
  exploit cache_up2date_res; eauto.
  intros (rpcl & rpct & rl & rt & H1 & H2 & H3 & H4).
  generalize (cache_hit_read_determ CREAD H4).
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

Ltac abstract_tag tag :=
  match goal with
    | H : labToZ ?l tag _ |- _ => l
  end.

Ltac quasi_abstract_labels opcode :=
  match goal with
    | H : context[cache_hit _ _ ?tags _] |- _ =>
      match tags with
        | (dontCare, dontCare, dontCare) =>
          constr:(<||> : Vector.t L (labelCount opcode))
        | (?t1, dontCare, dontCare) =>
          let l1 := abstract_tag t1 in
          constr:(<|l1|> : Vector.t L (labelCount opcode))
        | (?t1, ?t2, dontCare) =>
          let l1 := abstract_tag t1 in
          let l2 := abstract_tag t2 in
          constr:(<|l1; l2|> : Vector.t L (labelCount opcode))
        | (?t1, ?t2, ?t3) =>
          let l1 := abstract_tag t1 in
          let l2 := abstract_tag t2 in
          let l3 := abstract_tag t3 in
          constr:(<|l1; l2; l3|> : Vector.t L (labelCount opcode))
      end
    | |- _ => fail 1 "quasi_abstract_labels" opcode
  end.

Ltac analyze_cache_hit :=
  (* Find the current opcode, build the label vector use cache_up2date
  to build an equation about apply_rule. *)
  let opcode := get_opcode in
  match goal with
    | CACHE : cache_up2date _,
      CHIT : cache_hit ?tmuc _ ?tags ?pct,
      CREAD : cache_hit_read _ _ _ |- _ =>
      let vls := quasi_abstract_labels opcode in
      let pcl := abstract_tag pct in
      exploit (@analyze_cache_hit tmuc opcode vls tags pcl pct);
      unfold labsToZs, nth_labToZ; simpl; eauto;
      let rpcl := fresh "rpcl'" in
      let rl := fresh "rl'" in
      intros [rl [rpcl [? [? ?]]]]; subst
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
           | H : match_stk_elmt _ _ (CData _) |- _ => inv H
         end;
  repeat match goal with
           | H : match_atoms _ _ (?v, _) |- _ => inv H
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

(** Cache hit case *)

Lemma cache_hit_simulation :
  forall s1 s2 a2 s2'
         (Hmatch : match_states s1 s2)
         (Hs2' : priv s2' = false)
         (Hstep : cstep SysTable s2 a2 s2'),
    exists a1 s1', step_rules SysTable fetch_rule_g s1 a1 s1' /\
                   match_actions a1 a2 /\
                   match_states s1' s2'.
Proof.
  intros.
  inv Hmatch.
  destruct apc as [apc apcl].
  inv Hstep; simpl in *; try congruence;

  match_inv;

  on_case ltac:(first [instr OpLoad | instr OpStore])
          "Couldn't analyze Load or Store"
          ltac:(complete_exploit read_m_labToZ; match_inv);

  on_case ltac:(first [instr OpRet | instr OpVRet])
          "Couldn't analyze Ret cases"
          ltac:(complete_exploit match_stacks_c_pop_to_return);

  analyze_cache_hit;

  on_case ltac:(instr OpStore)
          "Couldn't construct memory update"
          ltac:(exploit upd_m_labToZ; eauto; try solve [constructor; eauto];
                intros [? [? ?]]);

  on_case ltac:(instr OpCall)
          "Couldn't exploit Call case"
          ltac:(idtac;
                match goal with
                  | MATCH : Forall2 (match_stk_elmt ?tmuc) ?aargs ?cargs,
                    ARGS : forall se, In se ?cargs -> _ |- _ =>
                    generalize (@match_stacks_data aargs cargs tmuc MATCH ARGS); intro
                end);

  (* For the BranchNZ case *)
  on_case ltac:(instr OpBranchNZ)
          "Case analysis for BranchNZ failed"
          ltac:(idtac;
                match goal with
                  | |- context[if (?z =? 0) then _ else _ ] =>
                    let H := fresh "H" in
                    assert (H := Z.eqb_spec z 0);
                    destruct (z =? 0);
                    inv H
                end);

  solve [
      eexists; eexists; split; try split;
      try (econstructor (solve [compute; eauto]));
      repeat (constructor; eauto); simpl; f_equal; intuition (auto 7)
    ].

Qed.

(** Cache miss case *)

Notation cstep := (cstep SysTable).
Notation runsUntilUser := (runsUntilUser SysTable).
Notation runsToEnd := (runsToEnd SysTable).
Notation runsToEscape := (runsToEscape SysTable).

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

Lemma update_cache_mem_eq_except_cache :
  forall cache o ts pct,
    mem_def_on_cache cache ->
    mem_eq_except_cache cache (update_cache o ts pct cache).
Proof.
  intros.
  split; auto.
  intros. unfold update_cache.
    rewrite index_list_Z_update_list_list_old; auto.
    destruct ts as [[t1 t2] t3].
    simpl.
    repeat match goal with
             | H : addr <> ?addr' |- _ => unfold addr' in H
           end.
    omega.
Qed.
Hint Resolve update_cache_mem_eq_except_cache.

Inductive syscall_at_state : CS -> Prop :=
| syscall_at_state_def: forall c m fh i s pc pcl id
    (INSTR:index_list_Z pc i = Some (SysCall id)),
    syscall_at_state (CState c m fh i s (pc,pcl) false).

Lemma configuration_at_miss :
  forall s1 s21 e2 s22
         (MATCH : match_states s1 s21)
         (STEP : cstep s21 e2 s22)
         (PRIV : priv s22 = true),
    (exists opcode (vls : Vector.t L (projT1 (fetch_rule_impl opcode))) ts pct,
      labsToZs vls (cache s22) ts /\
      labToZ (snd (apc s1)) pct (cache s22) /\
      cache s22 = update_cache (opCodeToZ opcode) ts pct (cache s21) /\
      mem s22 = mem s21 /\
      fhdl s22 = fhdl s21 /\
      imem s22 = imem s21 /\
      stk s22 = CRet (pc s21) false false :: stk s21 /\
      pc s22 = (0, handlerTag)) 
    \/ syscall_at_state s21.
Proof.
  intros.
  inv MATCH.
  inv STEP; simpl in *; try congruence;

  match_inv;

  on_case ltac:(first [instr OpLoad | instr OpStore])
          "Couldn't analyze Load case"
          ltac:(complete_exploit read_m_labToZ; match_inv);

  on_case ltac:(first [instr OpRet | instr OpVRet])
          "Couldn't analyze Ret cases"
          ltac:(complete_exploit match_stacks_c_pop_to_return);

  try (left;
  let opcode := get_opcode in
  let vls := quasi_abstract_labels opcode in
      exists opcode; exists vls;
      match goal with
        | H : context[cache_hit _ _ ?ts _] |- _ =>
          exists ts
      end;
      eexists; simpl; repeat econstructor;
      unfold nth_labToZ, Vector.nth_order; simpl;
        eapply labToZ_cache; eauto).

  (* SysCall case *)
  right; econstructor; eauto.
Qed.

Lemma update_cache_cache_hit :
  forall tmuc op ts pct,
    cache_hit (update_cache op ts pct tmuc) op ts pct.
Proof.
  unfold update_cache.
  intros.
  destruct ts as [[t1 t2] t3].
  econstructor; eauto; econstructor;
  rewrite index_list_Z_update_list_list; compute; reflexivity.
Qed.
Hint Resolve update_cache_cache_hit.

Lemma update_cache_spec_rvec_cache_hit :
  forall rpcl rl cache cache' op tags pc zpc zr
         (MATCH : handler_final_mem_matches rpcl rl cache cache' zpc zr)
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
  destruct MATCH as [m [H1' [H2' [H3' [RES UP]]]]].
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

Lemma handler_final_mem_matches_labToZ_preserved :
  forall l m m' z rpcl rl zpc zr,
    labToZ l z m ->
    mem_def_on_cache m ->
    handler_final_mem_matches rpcl rl m m' zpc zr ->
    labToZ l z m'.
Proof.
  intros.
  inv H1. intuition.
  exploit extends_mem_def_on_cache; eauto. intros Hx.
  unfold update_cache_spec_rvec in H6.
  eapply labToZ_cache; eauto.
  constructor; auto.
  intros.
  rewrite <- H6; eauto.
Qed.

Lemma handler_final_mem_matches_labsToZs_preserved :
  forall m m' n (vls: Vector.t L n) zz rpcl rl zpc zr,
    labsToZs vls m zz ->
    mem_def_on_cache m ->
    handler_final_mem_matches rpcl rl m m' zpc zr ->
    labsToZs vls m' zz .
Proof.
  intros. destruct zz as [[t1 t2] t3]. inv H. intuition.
  simpl. unfold nth_labToZ in *.
  destruct (le_lt_dec n 0);
  destruct (le_lt_dec n 1);
  destruct (le_lt_dec n 2); subst; intuition; eauto using handler_final_mem_matches_labToZ_preserved.
Qed.

Lemma cache_hit_mem_def_on_cache: forall m op ts pct,
                                    cache_hit m op ts pct ->
                                    mem_def_on_cache m.
Proof.
  intros. inv H. repeat (econstructor; eauto; intuition; eauto).
Qed.
Hint Resolve cache_hit_mem_def_on_cache.

(* This lemma says: if the rule table says "yes" for some inputs and
we start in kernel mode with a cache with those inputs, then the final
memory has an up-to-date cache w.r.t. those inputs. *)

Lemma handler_final_mem_cache_up2date :
  forall m2 m2' opcode (vls : Vector.t L (projT1 (fetch_rule_impl opcode))) ts pcl pct
         rpcl rl zpc zr
         (Hvls : labsToZs vls m2 ts) (Hpc : labToZ pcl pct m2)
         (HIT : cache_hit m2 (opCodeToZ opcode) ts pct)
         (OK : apply_rule (projT2 (fetch_rule_impl opcode)) pcl vls = Some (rpcl, rl))
         (MATCH : handler_final_mem_matches rpcl rl m2 m2' zpc zr),
    cache_up2date m2'.
Proof.
  intros.
  intros opcode' ts' pct' HIT'.
  exploit update_cache_spec_rvec_cache_hit; eauto.
  intros HIT''.
  generalize (cache_hit_unique HIT' HIT'').
  intros [E1 [E2 E3]].
  apply opCodeToZ_inj in E1. subst.
  exists vls. exists pcl. exists rpcl. exists zpc. exists rl. exists zr.
  simpl in OK. rewrite OK.
  apply cache_hit_mem_def_on_cache in HIT.
  exploit handler_final_mem_matches_labToZ_preserved; eauto. intro.
  exploit handler_final_mem_matches_labsToZs_preserved; eauto. intro.
  destruct MATCH; intuition eauto.
Qed.
Hint Resolve handler_final_mem_cache_up2date.

Lemma handler_final_mem_def_on_cache : forall c c' orl rpcl zpc zr
                                              (Hmatch: handler_final_mem_matches orl rpcl c c' zpc zr)
                                              (Hdef: mem_def_on_cache c),
                                         mem_def_on_cache c'.
Proof.
  intros.
  inv Hmatch. intuition.
  unfold update_cache_spec_rvec in *.
  destruct Hdef as [op [pctag [tag1 [tag2 [tag3 [tagr [tagrpc Hint]]]]]]]. intuition.
  inv H2.
  econstructor; eauto.
  repeat match goal with
      | H: tag_in_mem _ _ _ |- _  => inv H
      | H: tag_in_mem' _ _ _ |- _  => inv H
  end.
  unfold addrOpLabel, addrTagPC, addrTag1, addrTag2, addrTag3, addrTagRes, addrTagResPC in *.
  do 6 eexists ; intuition; eauto;
  repeat (econstructor; eauto); try (erewrite <- H4; eauto; try omega).
Qed.

Lemma update_cache_mem_def_on_cache : forall c c' op args pct,
                                        c' = (update_cache op args pct c) ->
                                        mem_def_on_cache c'.
Proof.
  intros.
  unfold update_cache in *.
  set (bc := build_cache op args pct) in *.
  assert (Hhit:= build_cache_hit op args pct); eauto.
  destruct args as [[t1 t2] t3]. fold bc in Hhit. simpl build_cache in *.
  specialize (index_list_Z_update_list_list' bc c) ; eauto. intros Hspec.
  rewrite <- H in Hspec.
  unfold bc at 1 in Hspec. simpl length in Hspec.
  exists op. exists pct. exists t1. exists t2. exists t3.
  exists dontCare; exists dontCare.
  unfold addrOpLabel, addrTagPC, addrTag1, addrTag2, addrTag3, addrTagRes, addrTagResPC in *.
  intuition;
  match goal with
    | |- tag_in_mem _ _ _ => repeat (econstructor; eauto; try omega) ; try (erewrite Hspec; eauto; try zify ; omega)
    | |- tag_in_mem' _ _ _ => exists handlerTag; try (erewrite Hspec; eauto); try zify ; omega
                                     end.
Qed.

Lemma handler_final_mem_matches_mem_eq_except_cache: forall rl rpcl m m'' zrpc rz,
  mem_def_on_cache m ->
  handler_final_mem_matches rl rpcl m m'' zrpc rz ->
  mem_eq_except_cache m m''.
Proof.
  destruct 2 as (m' & T1 & T2 & T3 & T4 & T5).
  unfold CodeSpecs.extends in *.
  split; auto.
  intros addr H0 H1 H2 H3 H4 H5 H6.
  unfold update_cache_spec_rvec in T5.
  rewrite <- T5; auto.
Qed.

Lemma match_atoms_extends : forall c1 c2 a1 a2
                                   (DEF : mem_def_on_cache c1)
                                   (ATOMS : match_atoms c1 a1 a2)
                                   (EXT : CodeSpecs.extends c1 c2),
                              match_atoms c2 a1 a2.
Proof.
  intros.
  inv ATOMS; constructor.
  eapply labToZ_cache; eauto.
  split; auto.
Qed.
Hint Resolve match_atoms_extends.

Lemma match_atoms_preserved :
  forall tmuc aa ca rl rpcl op ts pct tmuc' zrpc zr
         (DEF : mem_def_on_cache tmuc)
         (STKS : match_atoms tmuc aa ca)
         (MATCH : handler_final_mem_matches rl rpcl
                                            (update_cache (opCodeToZ op)
                                                          ts pct tmuc)
                                            tmuc'
                                            zrpc zr),
    match_atoms tmuc' aa ca.
Proof.
  intros tmuc aa ca rl rpcl op ts pct tmuc' zrpc zr DEF STKS MATCH.
  inv STKS; constructor.
  eapply labToZ_cache; eauto.
  assert (mem_eq_except_cache tmuc (update_cache (opCodeToZ op) ts pct tmuc)) by auto.
  assert (mem_eq_except_cache (update_cache (opCodeToZ op) ts pct tmuc) tmuc').
    eapply handler_final_mem_matches_mem_eq_except_cache; eauto.
  destruct H; destruct H0; split; auto.
Qed.

Lemma match_stacks_preserved :
  forall tmuc astk cstk rl rpcl op ts pct tmuc' zrpc zr
         (DEF : mem_def_on_cache tmuc)
         (STKS : match_stacks tmuc astk cstk)
         (MATCH : handler_final_mem_matches rl rpcl
                                            (update_cache (opCodeToZ op)
                                                          ts pct tmuc)
                                            tmuc'
                                            zrpc zr),
    match_stacks tmuc' astk cstk.
Proof.
  induction astk; destruct cstk; simpl; try constructor.
  - intros rl rpcl op ts pct tmuc' zrpc zr DEF STKS MATCH.
    inv STKS.
  - intros rl rpcl op ts pct tmuc' zrpc zr DEF STKS MATCH.
    inv STKS.
  - inv STKS.
    inv H2; constructor;
    eapply match_atoms_preserved; eauto.
  - eapply IHastk; eauto.
    inv STKS; auto.
Qed.

Lemma match_memories_extends : forall c1 c2 m1 m2
                                      (DEF : mem_def_on_cache c1)
                                      (MEMS : match_memories c1 m1 m2)
                                      (EXT : CodeSpecs.extends c1 c2),
                                 match_memories c2 m1 m2.
Proof.
  intros.
  induction MEMS; constructor; eauto.
Qed.

Lemma match_memories_preserved :
  forall tmuc amem cmem rl rpcl op ts pct tmuc' zrpc zr
         (DEF : mem_def_on_cache tmuc)
         (STKS : match_memories tmuc amem cmem)
         (MATCH : handler_final_mem_matches rl rpcl
                                            (update_cache (opCodeToZ op)
                                                          ts pct tmuc)
                                            tmuc'
                                            zrpc zr),
    match_memories tmuc' amem cmem.
Proof.
  intros tmuc amem cmem rl rpcl op ts pct tmuc' zrpc zr DEF STKS MATCH.
  inv STKS; constructor; auto.
  - eapply match_atoms_preserved; eauto.
  - revert H0; revert l'.
    induction l; destruct l'; intro HF; inv HF; constructor; auto.
    eapply match_atoms_preserved; eauto.
Qed.

Lemma cache_miss_simulation :
  forall s1 s21 e21 s22 s23
         (MATCH : match_states s1 s21)
         (STEP1 : cstep s21 e21 s22)
         (RUN : runsUntilUser s22 s23),
    match_states s1 s23 \/ syscall_at_state s21.
Proof.
  intros.
  exploit (@runsUntilUser_l _ SysTable); eauto.
  intros PRIV.
  exploit configuration_at_miss; eauto.
  destruct 1 as [EE|EE].
  - { left;
      destruct EE as [op [vls [ts [pct [Hvls [Hpc EQS]]]]]].
      destruct ts as [[t1 t2] t3].
      destruct s22; simpl in EQS, PRIV; subst.
      inv MATCH; simpl.
      intuition. subst.
      destruct (apply_rule (projT2 (fetch_rule_impl op)) (snd apc) vls)
        as [[orl rpcl]|] eqn:E.
      - exploit handler_correct_succeed; eauto.
        { eapply update_cache_cache_hit. }
        intros [cache' [zr [zrpc [ESCAPE1 MATCH']]]].
        exploit (@rte_success _ SysTable); eauto.
        intros ESCAPE2.
        unfold kernel_code, faultHandler, handler in *.
        generalize (runsToEscape_determ ESCAPE1 ESCAPE2).
        intros H. subst.
        constructor; eauto.
        + eapply handler_final_mem_cache_up2date; eauto.
          simpl.
          exploit update_cache_spec_rvec_cache_hit; simpl; eauto.
          simpl.
          apply update_cache_cache_hit.
        + simpl in MATCH'. 
          eapply handler_final_mem_def_on_cache; eauto.
        + eapply match_stacks_preserved; eauto.
        + eapply match_memories_preserved; eauto.
        + eapply match_atoms_preserved; eauto.
      - exploit handler_correct_fail; eauto.
        { eapply update_cache_cache_hit. }
        intros [stk' [cache' [ESCAPE1 EXT]]].
        inv ESCAPE1.
        + apply runsUntilUser_r in STAR. simpl in STAR. congruence.
        + exfalso.
          eapply kernel_run_success_fail_contra; eauto.
    }
  - right; auto. (* syscall *)
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
  [exploit (@priv_no_event_l _ SysTable); eauto; intros ?; subst|];
  (destruct (priv s') eqn:PRIV';
  [exploit (@priv_no_event_r _ SysTable); eauto; intros ?; subst|]);
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
  - exploit (@priv_no_event_r _ SysTable); eauto.
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

Require SOPCLattice.
Opaque SOPCLattice.joinPcode.

Lemma exec_cexec : forall id (is : id -> _) s t s',
                     (@TINI.exec (concrete_machine SysTable (faultHandler++SOPCLattice.joinPcode) is)) s t s' ->
                     cexec s t s'.
Proof.
  intros ik is s t s' Hexec.
  induction Hexec; eauto.
  eapply cexec_step with (e:=E e); eauto.
  eapply cexec_step with (e:=Silent); eauto.
Qed.

End CExec.

Inductive match_events : @Event L -> CEvent -> Prop :=
| me_intro : forall a1 a2 m
                    (MATCH : match_atoms m a1 a2),
               match_events (EInt a1) (CEInt a2 m).

Definition correct_syscall_implem :=
 forall id sys_info c m fh i args pc pcl s1 s s_u,
  length args = si_arity sys_info ->
  runsUntilUser (CState c m fh i (args ++ CRet (pc+1, pcl) true false :: s)
                        (si_pc sys_info, handlerTag) true) s_u ->
  match_states s1 (CState c m fh i (args ++ s) (pc, pcl) false) ->
  read_m pc i = Some (SysCall id) ->
  SysTable id = Some sys_info ->
   exists s1' : state (quasi_abstract_machine SysTable fetch_rule_g),
     step (quasi_abstract_machine SysTable fetch_rule_g) s1 Silent s1' /\
     match_states s1' s_u.

Variable correct_syscall_implem_hyp : correct_syscall_implem.

Lemma quasi_abstract_concrete_sref_prop : forall id (is : id -> _),
  @state_refinement_statement (quasi_abstract_machine SysTable fetch_rule_g)
                              (concrete_machine SysTable (faultHandler++SOPCLattice.joinPcode) is)
                              match_states match_events.
Proof.
  intros ik is s1 s2 t2 s2' MATCH EXEC. 
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
    destruct e1.
    + exists (e0::t1). eexists.
      split. econstructor 2; eauto.
      inv ME.
      constructor; auto.
      constructor; auto.
    + exists (t1). eexists.
      split. econstructor; eauto.
      inv ME.
      auto.

  - exploit cache_miss_simulation; eauto.
    destruct 1; eauto.
    (* syscall *)
    inv H2; inv H0; try congruence.
    assert (id0=id) by congruence; subst.
    edestruct correct_syscall_implem_hyp as (s1' & SS1 & SS2); eauto.
    destruct IHEXEC with s1' t2  as (t1 & s1'' & T2 & T3) ; auto.
    econstructor; econstructor; split.
    2: eauto.
    econstructor 3; eauto.
Qed.

Definition quasi_abstract_concrete_sref id is :=
  {| sref_prop := @quasi_abstract_concrete_sref_prop id is |}.

End RefQAC.

End StateRefinement.


(* Part of the proof specific to the right definition of initial_data for SOP *)
Section SOP.

Require Import SOPCLattice.

(* Initial data *)
Definition sop_cm_init_data :=
  (list Instr * list (Z * list Z) * nat)%type.

Definition add_set_repr (m : list (@Atom Z)) (a : Z * list Z) :=
  let '(_, ps) := a in
  m ++ (Z.of_nat (length ps), handlerTag)
    :: map (fun p => (p, handlerTag)) ps.

Definition sop_init_kernel_mem_aux (d : list (Z * list Z)) init :=
  fold_left add_set_repr d init.

(* we need to allocate a bottom tag to be able to tag the initial pc
   and the initial user memory *)
Definition initial_mem_segment :=
  ((0, handlerTag) :: nil).

Definition sop_init_kernel_mem (d : list (Z * list Z)) :=
  sop_init_kernel_mem_aux d initial_mem_segment.

Definition add_elmt_repr (acc : Z * list CStkElmt) (a : Z * list Z) :=
  let '(z, p) := a in
  let '(len, stk) := acc in
  (len + 1 + Z.of_nat (length p), (* previous length + one atom containing the size of p
                                     + p itself *)
   stk ++ (z, len) ::: nil).

(* Pushes on the stack the initial data, tagged with the arrays
allocated in sop_initial_kernel_mem *)
Definition sop_init_stack_aux (d : list (Z * list Z)) init :=
  fold_left add_elmt_repr d init.

Definition sop_init_stack (d : list (Z * list Z)) :=
  snd (sop_init_stack_aux d (Z.of_nat (length (initial_cache ++ initial_mem_segment)), nil)).

Definition sop_init_state (id : sop_cm_init_data) :=
  let '(p,d,n) := id in
  let bot := Z.of_nat (length initial_cache) in
  ( p, 
    sop_init_kernel_mem d, 
    replicate (0, bot) n,
    sop_init_stack d,
    bot
  ).

Definition sop_fault_handler := FaultRoutine.faultHandler (T:=Zset.t)
                                                          fetch_rule_impl.

Let SOPSysTable' := SOPSysTable sop_fault_handler.
Instance SOPwf' : WfConcreteLattice Zset.t ZsetLat SOPClatt SOPSysTable' := SOPwf sop_fault_handler.

Definition Zset_of_list (ps : list Z) : Zset.t :=
  fold_left (fun s p => Zset.add p s) ps Zset.empty.

Definition sop_am_init_stack (d : list (Z * list Z)) :=
  map (fun d => (fst d, Zset_of_list (snd d))) d.

Definition sop_concrete_machine :=
  concrete_machine (SOPSysTable sop_fault_handler) (sop_fault_handler++joinPcode) sop_init_state.

Inductive ac_match_initial_data :
  init_data (abstract_machine (SOPSysTable sop_fault_handler)) -> 
  init_data sop_concrete_machine -> Prop :=
| ac_mid : forall d2 p2 n2,
             ac_match_initial_data
               (p2, sop_am_init_stack d2, n2, bot)
               (p2, d2, n2).


Lemma match_stk_elmt_extends :
  forall cache se1 se2 cache'
         (SELMTS : match_stk_elmt cache se1 se2)
         (EXT : CodeSpecs.extends cache cache')
         (DEF : mem_def_on_cache cache),
    match_stk_elmt cache' se1 se2.
Proof.
  intros.
  inv SELMTS; constructor;
  inv ATOMS; constructor;
  eapply (@labToZ_extension_comp _ _ _ _ SOPwf'); eauto.
Qed.
Hint Resolve match_stk_elmt_extends.

Lemma match_stacks_extends :
  forall cache stk1 stk2 cache'
         (STKS : match_stacks cache stk1 stk2)
         (EXT : CodeSpecs.extends cache cache')
         (DEF : mem_def_on_cache cache),
    match_stacks cache' stk1 stk2.
Proof.
  induction 1 as [|se1 se2 stk1 stk2 SELMTS STKS IH]; intros; eauto.
  - constructor.
  - constructor; eauto.
    apply IH; eauto.
Qed.

Lemma memseq_add_at_end :
  forall xl mem  (z : Z),
    z = (length mem)%Z ->
    Arrays.memseq (mem ++ map (fun p => (p, handlerTag)) xl)
                  z xl.
Proof.
  induction xl ; intros.
  simpl. econstructor; eauto.
  subst. simpl.
  constructor. eapply index_list_Z_app; eauto.
  replace (mem++(a,handlerTag)::map (fun p => (p,handlerTag)) xl) with
          ((mem++((a,handlerTag)::nil))++map (fun p => (p,handlerTag)) xl).
  replace ((length mem) + 1) with (Z.of_nat (length (mem++((a,handlerTag)::nil)))).
  eapply (IHxl (mem++((a,handlerTag)::nil))
               ((Z.of_nat (length (mem++((a,handlerTag)::nil)))))); eauto.
  rewrite app_length. simpl. zify; omega.
  rewrite <- app_assoc; eauto.
Qed.

Lemma Zset_of_list_correct_gen :
  forall ps' ps init,
    (forall a, In a ps <-> Zset.In a init) ->
    (forall a, In a (ps ++ ps') <-> Zset.In a (fold_left (fun s p => Zset.add p s) ps' init)).
Proof.
  induction ps' as [|p ps' IH]; intros.
  - simpl. rewrite app_nil_r. auto.
  - simpl.
    rewrite <- (IH (ps ++ (p :: nil))).
    + rewrite <- app_assoc. reflexivity.
    + intros.
      rewrite Zset.In_add.
      rewrite in_app_iff. simpl. intuition.
      * right. apply H. eauto.
      * left. apply H. eauto.
Qed.

Lemma Zset_of_list_correct :
  forall ps, (forall a, In a ps <-> Zset.In a (Zset_of_list ps)).
Proof.
  intros ps.
  apply Zset_of_list_correct_gen with (ps := nil).
  unfold Zset.In.
  rewrite Zset.elements_empty. intuition.
Qed.
Hint Resolve Zset_of_list_correct.

Lemma match_init_stacks_gen :
  forall d2' d2 mem stk len stk'
         (DEF : mem_def_on_cache (initial_cache ++ mem))
         (RES : sop_init_stack_aux d2' (Z.of_nat (length (initial_cache++mem)), stk) 
                = (len, stk'))
         (MATCH : match_stacks (initial_cache ++ mem)
                               (map (fun a => AData a) (sop_am_init_stack d2))
                               stk),
    match_stacks (initial_cache ++ (sop_init_kernel_mem_aux d2' mem))
                 (map (fun a : Atom => AData a) (sop_am_init_stack (d2 ++ d2'))) stk'.
Proof.
  induction d2' as [|[xv xl] d2' IH].
  - simpl. intros.
    inv RES.
    rewrite app_nil_r. assumption.
  - intros. Opaque initial_cache.
    simpl in *.
    change (d2 ++ (xv, xl) :: d2') with (d2 ++ ((xv, xl) :: nil) ++ d2').
    rewrite app_assoc.
    eapply IH; eauto.
    + eapply extends_mem_def_on_cache; eauto.
      intros i v H.
      erewrite app_assoc.
      auto using index_list_Z_app2.
    + match goal with
        | H : sop_init_stack_aux d2' (?len, _) = _
          |- sop_init_stack_aux d2' (?len', _) = _ =>
          cut (len' = len)
      end.
      { intros H. rewrite H. eassumption. }
      rewrite app_length.
      rewrite app_length.
      rewrite Nat2Z.inj_add.
      rewrite Nat2Z.inj_add.
      simpl length.
      rewrite Nat2Z.inj_succ.
      rewrite map_length.
      rewrite app_length.
      zify; omega.
    + unfold sop_am_init_stack in *.
      rewrite map_app. rewrite map_app.
      apply Forall2_app.
      * eapply match_stacks_extends; eauto.
        intros i v H.
        erewrite app_assoc.
        eauto using index_list_Z_app2.        
      * simpl.
        repeat constructor.
        simpl.
        unfold labToZ.
        eexists xl.
        repeat (split; eauto).
        { econstructor; eauto.
          - rewrite app_assoc. rewrite index_list_Z_app; eauto.
          - match goal with
              | |- context[mem ++ ?a :: ?l] =>
                replace (mem ++ a :: l) with ((mem ++ (a :: nil)) ++ l)
            end.
            { rewrite app_assoc. apply memseq_add_at_end.
              rewrite app_length. rewrite app_length.
              rewrite app_length. rewrite Nat2Z.inj_add.
              simpl length. zify; omega.
            }
            rewrite <- app_assoc. reflexivity. }
        intros.
        Transparent initial_cache.
        rewrite app_length.
        rewrite Nat2Z.inj_add.
        unfold initial_cache. simpl length at 1.
        zify ; omega.
Qed.

Lemma match_init_stacks: forall d2,
 match_stacks (initial_cache ++ sop_init_kernel_mem d2)
              (map (fun a : Atom => AData a) (sop_am_init_stack d2))
              (sop_init_stack d2).
Proof.
  intros.
  unfold sop_init_kernel_mem.
  unfold sop_init_stack.
  destruct (sop_init_stack_aux d2
                               (Z.of_nat (length (initial_cache ++ initial_mem_segment)), nil))
    as [len stk] eqn:E.
  eapply match_init_stacks_gen with (d2 := nil); eauto.
  - intros. repeat eexists.
  - constructor. 
Qed.
Hint Resolve match_init_stacks.

Lemma replicate_mem_labToZ :
  forall l t km n,
    labToZ l t km ->
    match_memories km (replicate (0, l) n) (replicate (0, t) n).
Proof.
  unfold match_memories.
  induction n; intros; simpl; repeat constructor; eauto.
Qed.

Lemma sop_init_kernel_mem_com_app_acc: forall d2 m ic,
                                         ic ++ (sop_init_kernel_mem_aux d2 m) = 
                                         sop_init_kernel_mem_aux d2 (ic ++ m).
Proof.
  induction d2 as [|[x ps] d2 IH]; simpl; eauto.
  intros. rewrite IH.
  rewrite app_assoc.
  reflexivity.
Qed.
                                         
Lemma read_initial_mem :
  forall i d2,
    i < length (initial_cache ++ initial_mem_segment) ->
    index_list_Z i (initial_cache ++ (sop_init_kernel_mem d2)) = 
    index_list_Z i (initial_cache ++ initial_mem_segment).
Proof.
  intros.
  unfold sop_init_kernel_mem, sop_init_kernel_mem_aux.
  erewrite sop_init_kernel_mem_com_app_acc.
  gdep (initial_cache ++ initial_mem_segment).
  induction d2 as [|[x ps] d2 IH]; simpl; auto.
  intros.
  rewrite IH; eauto.
  - apply index_list_Z_app_lt; auto.
  - rewrite app_length.
    rewrite Nat2Z.inj_add.
    omega.
Qed.

Lemma initial_cache_no_hit :
  forall d2 opcode ts pct,
    ~ cache_hit (initial_cache ++ sop_init_kernel_mem d2) (opCodeToZ opcode) ts pct.
Proof.
  intros.
  intro contra.
  inv contra.
  clear - OP.
  inv OP.
  rewrite read_initial_mem in H.
  - compute in H.
    destruct opcode; congruence.
  - reflexivity.
Qed.

Lemma initial_mem_cache_def :
  forall d2,
    mem_def_on_cache (initial_cache ++ (sop_init_kernel_mem d2)).
Proof.
  intros d2.
  assert (mem_def_on_cache (initial_cache ++ initial_mem_segment)) by (repeat eexists).
  assert (CodeSpecs.extends (initial_cache ++ initial_mem_segment)
                            (initial_cache ++ sop_init_kernel_mem d2)).
  { unfold sop_init_kernel_mem.
    rewrite sop_init_kernel_mem_com_app_acc.
    clear H.
    gdep (initial_cache ++ initial_mem_segment).
    induction d2 as [|[x ps] d2 IH].
    - simpl. repeat intro; auto.
    - simpl.
      repeat intro.
      apply IH.
      apply index_list_Z_app2. assumption. }
  eapply extends_mem_def_on_cache; eauto.
Qed.
Hint Resolve initial_mem_cache_def.

Lemma fold_left_add_set_repr: forall l acc, 
                                exists l',
                                (fold_left add_set_repr l acc) = acc++l'.
Proof.
  induction l ; intros.
  simpl. exists nil. rewrite app_nil_r. auto.
  simpl. 
  edestruct (IHl (add_set_repr acc a)); eauto.
  rewrite H. destruct a; simpl.
  erewrite <- app_assoc; eauto. 
Qed.

Lemma initial_bottom :
  forall d2,
    labToZ bot 7 (initial_cache ++ (sop_init_kernel_mem d2)).
Proof.
  intros. 
  unfold sop_init_kernel_mem in *.
  rewrite sop_init_kernel_mem_com_app_acc.
  unfold initial_mem_segment, initial_cache.
  exists nil; intuition. 
  - repeat (econstructor; eauto).
    unfold sop_init_kernel_mem_aux.
    edestruct (fold_left_add_set_repr
                 d2 
                 (build_cache invalidOpCode (0, 0, 0) 0 ++ (0, handlerTag) :: nil)); eauto. 
    rewrite H. compute; auto.
  - compute in H.
    rewrite Zset.elements_empty in H. inv H. 
Qed.

Hint Resolve initial_bottom.

Lemma ac_match_initial_data_match_initial_states :
  forall ai ci,
    ac_match_initial_data ai ci ->
    @match_states _ _ _ (SOPSysTable sop_fault_handler)
                 joinPcode
                 (init_state (abstract_machine (SOPSysTable sop_fault_handler)) ai)
                 (init_state sop_concrete_machine ci).
Proof.
  intros ai ci H. inv H. 
  constructor; eauto.
  - repeat intro. exfalso.
    eapply initial_cache_no_hit; eauto.
  - unfold sop_init_kernel_mem.
    rewrite <- (app_nil_r initial_mem_segment).      
    erewrite <- sop_init_kernel_mem_com_app_acc.    
    induction n2; try solve [repeat constructor; eauto].    
    simpl. repeat (econstructor; simpl; eauto).
    + reflexivity.
    + intuition.
    + unfold Zset.In. rewrite Zset.elements_empty; eauto.
  - unfold sop_init_kernel_mem. 
    rewrite <- (app_nil_r initial_mem_segment).      
    erewrite <- sop_init_kernel_mem_com_app_acc.    
    repeat (econstructor; simpl; eauto). 
    + reflexivity.
    + intuition.
    +  unfold Zset.In. rewrite Zset.elements_empty; eauto.
  - unfold wf_systable. intros.
    unfold well_placed_syscall_implem.
    Opaque sop_fault_handler joinPcode faultHandler.
    unfold SOPSysTable in *. destruct id; try congruence. inv H.
    simpl. unfold kernel_code.
    eapply code_at_app. auto. 
Qed.

Transparent initial_cache.

Require Import Arrays.

Lemma cache_hit_mem_def_on_cache_inv :
  forall c1 c2 op ts pct
         (DEF : mem_def_on_cache c1)
         (EXT : CodeSpecs.extends c1 c2)
         (HIT : cache_hit c2 op ts pct),
    cache_hit c1 op ts pct.
Proof.
  intros.
  unfold mem_def_on_cache in *.
  repeat match goal with
           | H : exists _, _ |- _ => destruct H
         end.
  intuition.
  destruct HIT. subst.
  econstructor; eauto;
  repeat match goal with
           | H : tag_in_mem _ _ _ |- _ => destruct H
           | H : tag_in_mem' _ _ _ |- _ => destruct H
         end;
  constructor;
  match goal with
    | H1 : read_m ?addr c1 = Some ?X,
      H2 : read_m ?addr c2 = Some ?Y
      |- read_m ?addr c1 = Some ?Y =>
      clear - H1 H2 EXT;
      generalize (EXT _ _ H1);
      congruence
  end.
Qed.

(* Repeated lemma from FaultRoutine, needed to massage the unification *)
Lemma extension_comp_nth_labToZ : forall m1 m2 (n m:nat) (vls: Vector.t _ n) z,
    nth_labToZ vls m z m1 ->
    CodeSpecs.extends m1 m2 ->
    mem_def_on_cache m1 ->
    nth_labToZ vls m z m2.
Proof.
  unfold nth_labToZ; intros.
  destruct (le_lt_dec n m); eauto.
  eapply labToZ_extension_comp; eauto.
Qed.

Lemma labsToZs_extension_comp :
  forall m1 m2 n (vls : Vector.t _ n) ts
         (Hvls : labsToZs vls m1 ts)
         (EXT : CodeSpecs.extends m1 m2)
         (DEF : mem_def_on_cache m1),
    labsToZs vls m2 ts.
Proof.
  unfold labsToZs.
  intros m1 m2 n vls [[t1 t2] t3].
  intuition;
  eapply extension_comp_nth_labToZ; eauto.
Qed.
Hint Resolve labsToZs_extension_comp.

Lemma cache_hit_read_extends :
  forall c1 c2 rt rpct
         (EXT : CodeSpecs.extends c1 c2)
         (READ : cache_hit_read c1 rt rpct),
    cache_hit_read c2 rt rpct.
Proof.
  intros.
  destruct READ;
  repeat match goal with
           | H : tag_in_mem' _ _ _ |- _ => destruct H
         end.
  repeat econstructor; eauto.
Qed.

Lemma cache_up2date_extends : forall c1 c2
                                     (DEF : mem_def_on_cache c1)
                                     (UP2DATE : cache_up2date c1)
                                     (EXT : CodeSpecs.extends c1 c2),
                                cache_up2date c2.
Proof.
  intros.
  intros opcode ts pct HIT.
  exploit cache_hit_mem_def_on_cache_inv; eauto.
  clear HIT. intros HIT.
  exploit UP2DATE; eauto.
  intros (vls & pcl & rpcl & rpct & rl & rt & H1 & H2 & H3 & H4 & H5 & H6).
  eexists vls, pcl, rpcl, rpct, rl, rt.
  intuition; eauto using labToZ_extension_comp, cache_hit_read_extends.
Qed.

Lemma correct_syscall_implem_proof : 
  correct_syscall_implem joinPcode (SysTable:=SOPSysTable sop_fault_handler).
Proof.
  intros id sys_info c m fh i args pc pcl s1 s s_u T T0 T1 T2 T3.
  inv T1.
  assert (WF:=WFST _ _ T3).

  unfold SOPSysTable in T3.
  destruct id; try congruence ; match type of T3 with 
                   | Some ?a = Some ?c => assert (Heq: a = c) by congruence
               end. subst.

  destruct args as [|a [|b [|]]]; inv T.
  inv STKS.
  inv H3.  
  inv PC.
  unfold kernel_code in *.
  Transparent joinPcode.
  destruct a as [(a,la)|].
  destruct b as [(b,lb)|].
  inv H2; inv H4.
  inv ATOMS; inv ATOMS0.
  destruct TAG0 as (s1 & Hs11 & Hs12 & Hs13).
  destruct TAG1 as (s2 & Hs21 & Hs22 & Hs23).
  exploit (joinPcode_spec SOPSysTable' (pc+1,pcl) a la s1 b lb s2 s c); auto.
  apply WF.
  clear WF.
  intros (stk1 & cache1 & pc1 & priv1 & (t' & T4 & T5 & T6 & T7) & T1 & T8); subst.
  simpl in T1.
  destruct T1; subst.
  generalize (rte_success T0); intros TT0.
  generalize (runsToEscape_determ T8 TT0).
  intros E; inv E; clear TT0 T3 T0.
  exists (AState am i (AData (a, Zset.add b (Zset.union l2 l1)) :: l0) (pc+1,l)).
  split.
  replace (AData (a, l1) :: AData (b, l2) :: l0) with
  ((map AData ((a, l1) :: (b, l2) :: nil))++l0) by auto.
  eapply step_syscall; eauto.
  econstructor.
  simpl; auto.
  simpl; auto.
  constructor; eauto.
  - eapply cache_up2date_extends; eauto.
  - constructor; auto.
    + constructor.
      constructor.
      exists ((s2 ++ s1) ++ b :: nil); split; auto.
      split.
      * intro.
        repeat rewrite in_app_iff; simpl.
        rewrite Zset.In_add.
        rewrite Zset.In_union.
        rewrite <- Hs22.
        rewrite <- Hs12.
        intuition.
      * intros.
        destruct (Z_lt_dec 6 t'); try omega.
        elim T6.
        apply mem_def_on_cache_valid_address; auto.
        split; try omega.
        inv T5.
        eapply index_list_Z_some_pos; eauto.
    + eapply match_stacks_extends; eauto.
  - eapply match_memories_extends; eauto.
  - eapply match_atoms_extends; eauto.
    constructor; auto.

    Ltac inv_cstep := 
      match goal with
        | hc : cstep _ _ _ _ |- _ =>
          inv hc;
            simpl priv in *; try congruence;
            match goal with
              | h: read_m _ (_ ++ _) = Some _ |- _ => 
                rewrite index_list_Z_app in h; [inv h|auto;fail]
              | h: read_m _ (_ ++ _) = Some _ |- _ => 
                rewrite index_list_Z_app_general in h; [inv h|reflexivity]
              | h: read_m (_ + _ + _) (_ ++ _) = Some _ |- _ => 
                repeat rewrite Zplus_assoc_reverse in h;
                rewrite index_list_Z_app_general in h; [inv h|reflexivity]
            end
      end.

  - inv T0; inv_cstep.
    inv H1; inv_cstep.
    inv H16.
    inv H17.
    inv H6; inv_cstep.

  - inv T0; inv_cstep.
Qed.


Definition quasi_abstract_concrete_ref :
  refinement (quasi_abstract_machine (SOPSysTable sop_fault_handler) fetch_rule_g)
             sop_concrete_machine :=
  @refinement_from_state_refinement 
    _ _
    (quasi_abstract_concrete_sref correct_syscall_implem_proof sop_init_state)
     ac_match_initial_data 
     ac_match_initial_data_match_initial_states.

End SOP.


End MatchAbstractConcrete.

(** Combining the above into the final result *)
(** This is where we INSTANTIATE THE GENERIC REFINEMENT ! *)
Section RefAC.

Definition tini_fetch_rule_withsig :=
  (fun opcode => existT _
                        (labelCount opcode)
                        (fetch_rule opcode)).

Definition tini_match_states := match_states 
                                  (SysTable:=SOPSysTable (sop_fault_handler fetch_rule)) 
                                  fetch_rule.

Definition tini_concrete_machine : semantics := sop_concrete_machine fetch_rule.

Program Definition abstract_concrete_ref :
  refinement (abstract_machine (SOPSysTable (sop_fault_handler fetch_rule))) 
             tini_concrete_machine :=
  @ref_composition _ _ _
                   (abstract_quasi_abstract_ref (SOPSysTable 
                                                   (sop_fault_handler fetch_rule)))
                   (quasi_abstract_concrete_ref fetch_rule)
                   (@ac_match_initial_data fetch_rule)
                   match_events
                   _ _.

Next Obligation.
  eauto.
Qed.


End RefAC.
