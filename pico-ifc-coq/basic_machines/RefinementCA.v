(* The Abstract Machine refines the Concrete Machine (with appropriate fault handler). *)

Require Import Semantics.
Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Utils Lattices CLattices.

Require Import Instr.
Require Import AbstractCommon Rules QuasiAbstractMachine.

Require Import Concrete ConcreteMachine CodeGen CodeSpecs.
Require Import FaultRoutine.
Require Import Determinism.
Require Import ConcreteExecutions.
Require Import Refinement.
Require Import RefinementAC.
Require Import Encodable.

Set Implicit Arguments.
Local Open Scope Z_scope.

Axiom classic : forall P, P \/ ~P.

Section QuasiAbstractAbstract.

Context {T: Type}
        {Latt: JoinSemiLattice T}.

Program Definition quasi_abstract_abstract_sref :=
  @strong_refinement tini_quasi_abstract_machine
                     AbstractMachine.abstract_machine
                     eq eq _.
Next Obligation.
  exists a2. exists s22.
  repeat split; trivial.
  - generalize abstract_step_equiv. simpl. intuition.
    rewrite H. trivial.
  - destruct a2; constructor; trivial.
Qed.

Program Definition quasi_abstract_abstract_ref :=
  @refinement_from_state_refinement tini_quasi_abstract_machine
                                    AbstractMachine.abstract_machine
                                    quasi_abstract_abstract_sref eq
                                    _.

End QuasiAbstractAbstract.

Section Refinement.

Context {L: Type}
        {Latt: JoinSemiLattice L}
        {CLatt: ConcreteLattice L}
        {ELatt: Encodable L}
        {WFCLatt: WfConcreteLattice L Latt CLatt ELatt}.

(** The fault handler code and its correctness *)
Notation fetch_rule_g := fetch_rule. (* Should be able to replace this with a generic one later *)
Definition fetch_rule_withsig := (fun opcode => existT _ (labelCount opcode) (fetch_rule_g opcode)).
Definition faultHandler := FaultRoutine.faultHandler fetch_rule_withsig.

(* Bit more glue *)
Lemma handler_correct :
  forall m i s raddr c opcode vls pcl olr lpc,
  forall (INPUT: cache_hit c (opCodeToZ opcode) (@labsToZs L ELatt _ vls) (labToZ pcl))
         (RULE: apply_rule (fetch_rule_g opcode) pcl vls = Some (olr,lpc)),
    exists c',
    runsToEscape (CState c m faultHandler i (CRet raddr false false::s) (0,handlerTag) true)
                 (CState c' m faultHandler i s raddr false) /\
    handler_final_mem_matches (T:=L) olr lpc c c'.
Proof.
  intros.
  exploit (@handler_correct_succeed _ _ _ _ _ fetch_rule_withsig opcode); eauto.
Qed.

Lemma match_stacks_args' : forall args s cs,
   match_stacks (args ++ s) cs ->
   exists args' cs', cs = args'++cs'
                      /\ match_stacks args args'
                      /\ match_stacks s cs'.
Proof.
  induction args; intros.
  - simpl in *. exists nil; exists cs. repeat (split; eauto). constructor.
  - simpl in *.
    inv H.
    + exploit IHargs; eauto; intros [args' [cs' [Heq [Hmatch Hmatch']]]]; subst.
      exists (atom_labToZ a0 ::: args').
      eexists; split; eauto ; try reflexivity.
      split; eauto.
      constructor; eauto.
    + exploit IHargs; eauto; intros [args' [cs' [Heq [Hmatch Hmatch']]]]; subst.
      exists (CRet (atom_labToZ a0) r false :: args').
      eexists; split; eauto ; try reflexivity.
      split; eauto.
      constructor; eauto.
Qed.

Lemma match_stacks_data' : forall s cs,
    match_stacks s cs ->
    (forall a, In a s -> exists d : Atom, a = AData d) ->
    (forall a, In a cs -> exists d : Atom, a = CData d).
Proof.
  induction 1;  intros.
  - inv H0.
  - inv H2.  eauto.
    eapply IHmatch_stacks; eauto.
    intros; eapply H1; eauto.
    econstructor 2; eauto.
  - inv H2.
    eelim (H1 (ARet a r)); eauto. intros. congruence.
    constructor; auto.
    eapply IHmatch_stacks; eauto.
    intros; eapply H1; eauto.
    econstructor 2; eauto.
Qed.

Lemma match_stacks_pop_to_return : forall dstk cdstk pcv pcl b stk cs p,
   match_stacks (dstk  ++ ARet (pcv, pcl)        b   :: stk)
                (cdstk ++ CRet (pcv, labToZ pcl) b p :: cs) ->
   (forall e, In e dstk -> exists a, e = AData a) ->
   length dstk = length cdstk ->
   pop_to_return   (dstk  ++ ARet (pcv, pcl)        b   :: stk) (ARet (pcv, pcl) b :: stk) ->
   c_pop_to_return (cdstk ++ CRet (pcv, labToZ pcl) b p :: cs)  (CRet (pcv, labToZ pcl) b p ::cs).
Proof.
  intros.
  exploit match_stacks_app_length; eauto. intros [Hmatch Hmatch'].
  inv Hmatch'. inv H10.
  assert (Hcdstk:= match_stacks_data' Hmatch H0); eauto.
  eapply c_pop_to_return_pops_data; eauto.
Qed.

(** Observing a concete cache is just projecting it a the abstract level.
    Defining related notions and conversions
 *)
Fixpoint c_to_a_stack (cs : list CStkElmt): list (@StkElmt L) :=
  match cs with
    | nil => nil
    | CData s :: cs => (AData (atom_ZToLab s))::(c_to_a_stack cs)
    | CRet a r p::cs => ARet (atom_ZToLab a) r::(c_to_a_stack cs)
  end.

Lemma match_stacks_obs : forall s s',
    match_stacks s s' ->
    c_to_a_stack s' = s.
Proof.
  induction s ; intros.
  inv H; simpl; auto.
  inv H; simpl; rewrite IHs; eauto;
  rewrite <- atom_ZToLab_labToZ_id; auto.
Qed.

Hint Rewrite match_stacks_obs.

Definition observe_cstate (cs: CS) : @AS L :=
  match cs with
    | CState c m fh i s pc p =>
      AState (mem_ZToLab m) i (c_to_a_stack s) (atom_ZToLab pc)
  end.

Lemma handler_cache_hit_read :
  forall rl m rpcl tmuc,
    handler_final_mem_matches rpcl rl m tmuc ->
    cache_hit_read tmuc (labToZ rl) (labToZ rpcl).
Proof.
  intros; inv H ; auto.
Qed.

Ltac allinv' :=
  allinv ;
    (match goal with
       | [ H1:  ?f _ _ = _ ,
           H2:  ?f _ _ = _ |- _ ] => rewrite H1 in H2 ; inv H2
     end).

Lemma handler_final_cache_hit_preserved:
  forall tmuc tmuc' rl opcode labs rpcl pcl,
    handler_final_mem_matches rpcl rl tmuc tmuc' ->
    cache_hit tmuc  opcode labs pcl ->
    cache_hit tmuc' opcode labs pcl.
Proof.
  intros until 0. intros Hfinal HCHIT. inv HCHIT.
  inv Hfinal. unfold update_cache_spec_rvec in *.
  assert (exists tagr tagrpc, cache_hit_read tmuc' tagr tagrpc)
    by (eexists; eexists; eauto).
  destruct H1 as [tagr' [tagrpc' C]].
  inv C.
  repeat (match goal with
    | [ HTAG : tag_in_mem _ ?addr _ |- _ ] => inv HTAG
  end).
  econstructor;
  try solve [econstructor;
              try (rewrite <- H0; eauto;
                   match goal with
                     | [ |- ?a <> ?b ] => try (unfold a, b ; congruence)
                   end; fail); eauto];
  eauto.
Qed.

Lemma opCodeToZ_inj: forall o1 o2, opCodeToZ o1 = opCodeToZ o2 -> o1 = o2.
Proof.
  intros o1 o2 Heq.
  destruct o1, o2; inv Heq; try congruence.
Qed.

Hint Constructors cstep runsToEscape match_stacks match_states.

Ltac inv_cache_update :=
  unfold cache_up2date in *;
  unfold cache_up2date_weak; intros;
  exploit handler_final_cache_hit_preserved; eauto; intros;
  let P1 := fresh in let P2 := fresh in let P3 := fresh in
  match goal with
    |  [CHIT: cache_hit ?C _ _ _,
        CHIT': cache_hit ?C _ _ _ |- _] =>
       destruct (cache_hit_unique CHIT CHIT') as [P1 [P2 P3]];
       subst;
       apply opCodeToZ_inj in P1; subst;
       apply labsToZs_inj in P2; try (zify; omega); subst;
       apply labToZ_inj in P3 ;subst
   end;
  try allinv';
  try match goal with
        | [H : apply_rule _ _ _ = _ |- _] =>
          rewrite H
      end;
  try solve [eapply handler_cache_hit_read; eauto].

Lemma match_observe:
  forall s1 s2,
    match_states fetch_rule_g s1 s2 ->
    s1 = observe_cstate s2.
Proof.
  intros.
  inv H.
  simpl. erewrite match_stacks_obs; eauto.
  rewrite <- atom_ZToLab_labToZ_id.
  rewrite <- mem_ZToLab_labToZ_id.
  auto.
Qed.

Hint Constructors star plus.

Lemma update_list_map : forall xv rl m n m',
   update_list n (xv, rl) m = Some m' ->
   update_list n (xv, labToZ rl) (mem_labToZ m) = Some (mem_labToZ m').
Proof.
  induction m ; intros; simpl in *.
  destruct n ; simpl in *; inv H.
  destruct n ; simpl in *.
  - inv H. reflexivity.
  - case_eq (update_list n (xv,rl) m); intros; rewrite H0 in *; inv H.
    erewrite IHm ; eauto. reflexivity.
Qed.

Lemma upd_m_mem_labToZ : forall m addrv xv rl m',
  upd_m addrv (xv, rl) m = Some m' ->
  upd_m addrv (xv, labToZ rl) (mem_labToZ m) = Some (mem_labToZ m').
Proof.
  unfold upd_m.
  intros; simpl in *.
  case (addrv <? 0) in *. inv H.
  eapply update_list_map; eauto.
Qed.

Ltac renaming :=
  match goal with
    | [ Hrule : ifc_run_tmr _ ?opcode ?pcl ?v = Some (?rpcl, ?rl) |- _ ]  =>
      set (tags := labsToZs v);
      set (op := opCodeToZ opcode);
      set (pct := labToZ pcl);
      set (rpct := labToZ rpcl);
      set (rt := labToZ rl)
  end;
  match goal with
    | [ HH: match_states _ (AState ?m _ _ _) _ |- _ ] => set (cm := mem_labToZ m)
  end.

Ltac solve_read_m :=
  (unfold nth_labToZ; simpl);
  (unfold Vector.nth_order; simpl);
  (eapply read_m_labToZ; eauto).

Ltac res_label :=
  try match goal with
    | [Hrule: apply_rule _ _ _ = Some (_,_),
       Hcache : cache_up2date_weak _ _,
       CHIT : cache_hit _ _ _ _ |- _ ] =>
      let ASSERT := fresh "Assert" in
      assert (ASSERT := Hcache _ _ _ _ _ Hrule CHIT); eauto;
      simpl in ASSERT;
      inv ASSERT
      end.

Lemma update_cache_hit :
  forall opcode tags pctag tmuc,
    cache_hit (update_cache opcode tags pctag tmuc) opcode tags pctag.
Proof.
  intros.
  destruct tags as [[t1 t2] t3].
  econstructor; econstructor; unfold update_cache;
  rewrite index_list_Z_update_list_list;
  reflexivity.
Qed.

Ltac build_cache_and_tmu :=
  simpl;
  match goal with
    | [Hmiss: ~ cache_hit ?tmuc ?op ?tags ?pct ,
       Hrule: apply_rule _ _ _ = Some _ ,
       i : list Instr
     |- context[ (CState _ ?cm _ _ ?cstk (?pcv,_) _) ] ] =>
      let CHIT := fresh "CHIT" in
      set (tmuc':= update_cache op tags pct tmuc);
      assert (CHIT : cache_hit tmuc' op tags pct)
        by (eauto using update_cache_hit);
      edestruct (handler_correct cm i cstk (pcv,pct) _ _ CHIT Hrule) as [c [Hruns Hmfinal]];
      eauto
  end.

Hint Resolve match_stacks_app match_stacks_data' match_stacks_length.

Definition op_cons_ZToLab (oe: Event+τ) (t: list CEvent) :=
  match oe with
    | E (EInt e) => (CEInt (atom_labToZ e))::t
    | Silent => t
  end.

Lemma op_cons_ZToLab_none : (op_cons_ZToLab Silent nil) = (op_cons Silent (@nil CEvent)).
Proof. reflexivity. Qed.

Ltac hint_event := rewrite op_cons_ZToLab_none.

Ltac priv_steps :=
  match goal with
    | [Hruns : runsToEscape ?s ?s',
       Hmfinal: handler_final_mem_matches _ _ _ _ |- _ ] =>
      (eapply runsToEscape_plus in Hruns; [| congruence]);
        let Hll := fresh "Hll" in
        let Hspec := fresh "Hspec" in
      (generalize Hmfinal; intros [Hll Hspec]; inv Hll);
      (simpl atom_labToZ);
      (eapply plus_trans with (s2:= s) (t:= @nil CEvent); eauto);
      try (match goal with
          | [ |- cstep _ _ _ ] =>
            econstructor (solve [ eauto | eauto; solve_read_m ])
          | [ |- cstep _ _ _ ] =>
            econstructor ; eauto
           end);
      try match goal with
            | [ |- plus _ _ _ _ ] =>
              (eapply plus_right with (s2:= s') (t:= nil) (e:= Silent); eauto);
              (econstructor (solve [eauto;
                                    try (eapply handler_final_cache_hit_preserved; eauto);
                                    try (solve_read_m; eauto)]))
          end
  end.

Require Import Refinement.
Require RefinementAC.

Lemma step_preserved:
  forall s1 s1' e s2,
    step_rules (ifc_run_tmr fetch_rule_g) s1 e s1' ->
    match_states fetch_rule_g s1 s2 ->
    (exists s2', plus (step (concrete_machine faultHandler)) s2 (op_cons_ZToLab e nil) s2' /\ match_states fetch_rule_g s1' s2').
Proof.
  intros s1 s1' e s2 Hstep Hmatch.
  inv Hstep; renaming;
  match goal with
    | [Htmr : ifc_run_tmr _ _ _ _ = _ ,
       Hmatch : match_states _ _ _ |- _ ] =>
      inv Hmatch;
      unfold ifc_run_tmr in Htmr
  end;
  generalize (cache_up2date_success CACHE);
  intros CACHE'.

  - Case "Noop".
    destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
    + exists (CState tmuc cm faultHandler i cstk (pcv+1, pct) false).
      res_label. subst pct.
      inv H0.
      split; eauto.
      hint_event.
      eapply plus_step; eauto; eapply cstep_nop; eauto.
      econstructor; eauto.

    + build_cache_and_tmu. res_label.
      exists (CState c cm faultHandler i cstk (pcv+1, rpct) false). split.
      * priv_steps.
      * econstructor; eauto.
        inv_cache_update.

 - Case "Add".
   inv STKS. inv H3.
   destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc cm faultHandler i ((x1v+x2v,rt):::cs0) (pcv+1,rpct) false).
     split.
     * eapply plus_step ; eauto. eapply cstep_add ; eauto.
       eapply CACHE' with (1:= H0); eauto.
       auto.
     * eauto.
       econstructor; eauto.
   + build_cache_and_tmu.
     exists (CState c cm faultHandler i ((CData (x1v+x2v,rt))::cs0) (pcv+1, rpct) false).
     split.
     * priv_steps.
     * econstructor ; eauto.
       inv_cache_update.

 - Case "Sub".
   inv STKS. inv H3.
   destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc cm faultHandler i ((x1v-x2v,rt):::cs0) (pcv+1,rpct) false).
     split.
     * eapply plus_step ; eauto. eapply cstep_sub ; eauto.
       eapply CACHE' with (1:= H0); eauto. auto.
     * eauto.
       econstructor; eauto.
   + build_cache_and_tmu.
     exists (CState c cm faultHandler i ((x1v-x2v,rt):::cs0) (pcv+1, rpct) false).
     split.
     * priv_steps.
     * econstructor ; eauto.
       inv_cache_update.

- Case "Push ".
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc cm faultHandler i ((cv,rt):::cstk) (pcv+1,rpct) false).
     split.
     * eapply plus_step ; eauto. eapply cstep_push ; eauto.
       eapply CACHE' with (1:= H0); eauto. auto.
     * eauto.
       econstructor; eauto.
   + build_cache_and_tmu.
     exists (CState c cm faultHandler i ((cv,rt):::cstk) (pcv+1, rpct) false). split.
     * priv_steps.
     * econstructor ; eauto.
       inv_cache_update.

- Case "Pop".
  inv STKS.
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
  + exists (CState tmuc cm faultHandler i cs (pcv+1,rpct) false).
    hint_event.
    split; eauto.
    eapply plus_step; eauto.
    eapply cstep_pop; eauto.
    eapply CACHE' with (1:=H0); eauto.
    econstructor; eauto.
  + build_cache_and_tmu.
    exists (CState c cm faultHandler i cs (pcv+1, rpct) false). split.
    * priv_steps.
    * econstructor; eauto.
      inv_cache_update.

- Case "Load ".
  inv STKS.
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc cm faultHandler i ((xv,rt):::cs) (pcv+1,rpct) false).
     split.
     * eapply plus_step ; eauto.
       eapply cstep_load ; eauto.
       eapply CACHE' with (1:= H1); eauto.
       solve_read_m. auto.
     * eauto.
       econstructor; eauto.
   + build_cache_and_tmu.
     exists (CState c cm faultHandler i ((xv,rt):::cs) (pcv+1, rpct) false). split.
     * priv_steps. reflexivity.
     * econstructor ; eauto.
       inv_cache_update.

- Case "Store ".
  inv STKS. inv H5.
  exploit upd_m_mem_labToZ ; eauto. intros Hcm'.
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc (mem_labToZ m') faultHandler i cs0 (pcv+1,rpct) false).
     split.
     * eapply plus_step ; eauto.
       eapply cstep_store  ; eauto.
       eapply CACHE' with (1:= H2); eauto.
       solve_read_m. auto.
     * econstructor; eauto.
   + build_cache_and_tmu.
     exists (CState c (mem_labToZ m') faultHandler i cs0 (pcv+1, rpct) false). split.
     * priv_steps. reflexivity.
     * econstructor ; eauto.
       inv_cache_update.

- Case " Jump ".
  inv STKS.
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc cm faultHandler i cs (pcv',rpct) false).
     split.
     * eapply plus_step ; eauto. simpl.
       res_label. hint_event. reflexivity.
     * econstructor; eauto.
   + build_cache_and_tmu. res_label.
     exists (CState c cm faultHandler i cs (pcv', rpct) false). split.
     * priv_steps.
     * econstructor ; eauto.
       inv_cache_update.

- Case " Branch ".
  inv STKS.
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc cm faultHandler i cs
                    (if 0 =? 0 then pcv+1 else pcv+offv , rpct) false).
     split.
     * eapply plus_step ; eauto. res_label.
       eapply cstep_bnz ; eauto. auto.
     * econstructor; eauto.
   + build_cache_and_tmu.
     res_label.
     exists (CState c cm faultHandler i cs
                    (if 0 =? 0 then pcv+1 else pcv+offv , rpct) false).
     split.
     * res_label. priv_steps.
     * econstructor ; eauto.
       inv_cache_update.

- Case " Branch YES ".
  inv STKS.
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc cm faultHandler i cs
                    (if av =? 0 then pcv+1 else pcv+offv , rpct) false).
     split.
     * eapply plus_step ; eauto. res_label.
       eapply cstep_bnz ; eauto. auto.
     * econstructor; eauto.
       case_eq (av =? 0)%Z; intros; auto.
       eelim H1; eauto.
       rewrite Z.eqb_eq in H2. auto.
   + build_cache_and_tmu. res_label.
     exists (CState c cm faultHandler i cs
                    (if av =? 0 then pcv+1 else pcv+offv , rpct) false).
     split.
     * priv_steps.
     * econstructor ; eauto.
       inv_cache_update.
       case_eq (av =? 0)%Z; intros; auto.
       eelim H1; eauto.
       rewrite Z.eqb_eq in H2. auto.

- Case " Call ".
  inv STKS.
  edestruct (match_stacks_args' _ _ H4) as [args' [cs' [Heq [Hargs Hcs]]]]; eauto.
  inv Heq.
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc cm faultHandler i
                    (args'++ (CRet (pcv+1, rt) r false)::cs') (pcv',rpct) false).
     split.
     * eapply plus_step; eauto.
       eapply cstep_call ; eauto.
       eapply CACHE' with (1:= H0); eauto. auto.
     * econstructor; eauto.
   + build_cache_and_tmu.
     exists (CState c cm faultHandler i
                    (args'++ (CRet (pcv+1, rt) r false)::cs') (pcv',rpct) false).
     split.
     * priv_steps.
     * econstructor ; eauto.
       inv_cache_update.

- Case " Ret ".
  exploit @pop_to_return_spec; eauto.
  intros [dstk [stk [a [b [Heq Hdata]]]]]. inv Heq.
  exploit @pop_to_return_spec2; eauto. intros Heq. inv Heq.
  exploit @pop_to_return_spec3; eauto. intros Heq. inv Heq.

  edestruct (match_stacks_args' _ _ STKS) as [args' [cs' [Heq [Hargs Hcs]]]]; eauto.
  inv Heq. inv Hcs. simpl atom_labToZ in *.

  exploit match_stacks_pop_to_return; eauto.
  erewrite match_stacks_length; auto.
  intros.

  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
  + exists (CState tmuc cm faultHandler i cs (pcv',rpct) false).
     split.
     * simpl. res_label.
     * econstructor; eauto.

   + build_cache_and_tmu.
     exists (CState c cm faultHandler i cs (pcv',rpct) false). res_label.
     split.
     * priv_steps.
     * econstructor ; eauto.
       inv_cache_update.

- Case " VRet ".
  inv STKS.
  exploit @pop_to_return_spec; eauto.
  intros [dstk [stk [a [b [Heq Hdata]]]]]. inv Heq.
  exploit @pop_to_return_spec2; eauto. intros Heq. inv Heq.
  exploit @pop_to_return_spec3; eauto. intros Heq. inv Heq.
  edestruct (match_stacks_args' _ _ H4) as [args' [cs' [Heq [Hargs Hcs]]]]; eauto.
  inv Heq. inv Hcs. simpl atom_labToZ in *.
  exploit match_stacks_pop_to_return; eauto.
  erewrite match_stacks_length; auto.
  intros.

  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc cm faultHandler i (CData (resv,rt)::cs) (pcv',rpct) false).
     split.
     * eapply plus_step ; eauto.
       eapply cstep_vret ; eauto.
       eapply CACHE' with (1:= H1); eauto. auto.
     * econstructor; eauto.
   + build_cache_and_tmu.
     exists (CState c cm faultHandler i (CData (resv,rt)::cs) (pcv',rpct) false).
     split.
     * (eapply runsToEscape_plus in Hruns; [| congruence]);
       (generalize Hmfinal; intros [Hll Hspec]; inv Hll);
       (simpl atom_labToZ).
       (eapply plus_trans with (s2:= (CState tmuc' (mem_labToZ m) faultHandler i
                                             (CRet (pcv, pct) false false
                                                   :: (resv, labToZ resl)
                                                   ::: args' ++ CRet (pcv', labToZ pcl') true false :: cs)
                                             (0, handlerTag) true)); eauto).
       eapply plus_right ; eauto.
       eapply cstep_vret; eauto.
       eapply handler_final_cache_hit_preserved; eauto.
       reflexivity.
     * econstructor ; eauto.
       inv_cache_update.

- Case " Output ".
  inv STKS.
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc cm faultHandler i cs (pcv+1,rpct) false).
     split.
     * eapply plus_step ; eauto.
       eapply cstep_out ; eauto.
       eapply CACHE' with (1:= H0); eauto. auto.
     * econstructor; eauto.
   + build_cache_and_tmu.
     exists (CState c cm faultHandler i cs (pcv+1, rpct) false).
     split.
     *
       (eapply runsToEscape_plus in Hruns; [| congruence]);
       (generalize Hmfinal; intros [Hll Hspec]; inv Hll);
       (simpl atom_labToZ).
       (eapply plus_trans ; eauto).
       eapply plus_right ; eauto.
       eapply cstep_out; eauto.
       eapply handler_final_cache_hit_preserved; eauto.
       simpl.
       reflexivity.
     * econstructor ; eauto.
       inv_cache_update.
Qed.


Lemma plus_exec :
  forall (S : semantics) s t s',
    plus (step S) s t s' ->
    TINI.exec s t s'.
Proof.
  induction 1 as [s t s' [e|] STEP E|s s' s'' [e|] t t' STEP PLUS IH E]; simpl in *; subst; eauto.
Qed.

Lemma exec_trans :
  forall (S : semantics) (s : Semantics.state S) t1 s' t2 s''
         (E1 : TINI.exec s t1 s')
         (E2 : TINI.exec s' t2 s''),
    TINI.exec s (t1 ++ t2) s''.
Proof. induction 1; simpl; eauto. Qed.

Lemma concrete_quasi_abstract_sref_prop :
  state_refinement_statement (concrete_machine faultHandler)
                             (ifc_quasi_abstract_machine fetch_rule_g)
                             (fun cs qas => match_states fetch_rule_g qas cs)
                             (fun e1 e2 => RefinementAC.match_events e2 e1).
Proof.
  intros s1 s2 t2 s2' MATCH EXEC.
  gdep s1.
  induction EXEC as [s2|s2 e2 s2' t2 s2'' STEP EXEC IH|s2 s2' t2 s2'' STEP EXEC IH]; intros.
  - eexists nil.
    exists s1.
    split; constructor.
  - exploit step_preserved; eauto.
    intros [s1' [PLUS MATCH']].
    exploit IH; eauto.
    intros [t1 [s1'' [EXEC' MATCH'']]].
    exists (op_cons_ZToLab (E e2) t1).
    exists s1''.
    destruct e2 as [e2].
    split.
    + exploit plus_exec; eauto.
      simpl.
      intros.
      exploit exec_trans; eauto.
    + simpl. constructor; eauto.
      destruct e2. reflexivity.
  - exploit step_preserved; eauto.
    intros [s1' [PLUS MATCH']].
    exploit IH; eauto.
    intros [t1 [s1'' [EXEC' MATCH'']]].
    exists (op_cons_ZToLab Silent t1).
    exists s1''.
    split; eauto.
    exploit plus_exec; eauto.
    simpl.
    intros.
    exploit exec_trans; eauto.
Qed.

Definition concrete_quasi_abstract_sref :=
  {| sref_prop := concrete_quasi_abstract_sref_prop |}.

Definition concrete_quasi_abstract_ref :
  refinement (concrete_machine faultHandler)
             (ifc_quasi_abstract_machine fetch_rule_g) :=
  @refinement_from_state_refinement _ _
                                    concrete_quasi_abstract_sref
                                    (fun i1 i2 => ac_match_initial_data i2 i1)
                                    (fun i1 i2 => @ac_match_initial_data_match_initial_states _ _ _ _ _ i2 i1).

Lemma step_preserved_observ:
  forall s1 e s1' s2,
    step_rules (ifc_run_tmr fetch_rule_g) s1 e s1' ->
    match_states fetch_rule_g s1 s2 ->
    s1 = observe_cstate s2 /\ (exists s2', plus cstep s2 (op_cons_ZToLab e nil) s2' /\ match_states fetch_rule_g s1' s2').
Proof.
  intros.
  split.
  apply match_observe; auto.
  eapply step_preserved; eauto.
Qed.

(*
Lemma succ_preserved:
  forall s1 s2,
    match_states s1 s2 ->
    (success s1 <-> c_success s2).
Proof.
  induction 1; intros.
  split;
    ((unfold success, c_success; simpl);
     (inv MEM);
     (destruct apc; simpl);
     (destruct (read_m z i); intuition);
     (destruct i0 ; intuition)).
Qed.
*)

End Refinement.

(** Combining the above into the final result *)
(** This is where we INSTANTIATE THE GENERIC REFINEMENT *)
Section RefCA.

Context {observer: Type}
        {Latt: JoinSemiLattice observer}
        {CLatt: ConcreteLattice observer}
        {ELatt : Encodable observer}
        {WFCLatt: WfConcreteLattice observer Latt CLatt ELatt}.

Definition tini_fetch_rule_withsig :=
  (fun opcode => existT _
                        (QuasiAbstractMachine.labelCount opcode)
                        (QuasiAbstractMachine.fetch_rule opcode)).
Definition tini_faultHandler := FaultRoutine.faultHandler tini_fetch_rule_withsig.
Definition tini_match_states := match_states QuasiAbstractMachine.fetch_rule.

Program Definition concrete_abstract_ref :
  refinement tini_concrete_machine AbstractMachine.abstract_machine :=
  @ref_composition _ _ _
                   concrete_quasi_abstract_ref
                   quasi_abstract_abstract_ref
                   (fun i1 i2 => @ac_match_initial_data _ _ _ _ fetch_rule i2 i1)
                   (fun e1 e2 => match_events e2 e1)
                   _ _.

Next Obligation.
  eauto.
Qed.

End RefCA.
