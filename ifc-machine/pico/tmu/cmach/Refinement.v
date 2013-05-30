Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Utils Lattices CLattices WfCLattices.

Require Import TMUInstr.
Require Import Abstract Rules QuasiAbstractMachine.
Require Import AbstractCommon.

Require Import Concrete ConcreteMachineSmallStep CodeGen CodeSpecs.
Require Import FaultRoutine.
Require Import Determinism.
Require Import CExec.
Require Import Simulation.

Set Implicit Arguments.
Local Open Scope Z_scope. 
Coercion Z_of_nat : nat >-> Z.

Section Refinement.

Context {L: Type}
        {Latt: JoinSemiLattice L}
        {CLatt: ConcreteLattice L}
        {WFCLatt: WfConcreteLattice L Latt CLatt}.

(** The fault handler code and its correctness *)
Definition fetch_rule_withsig := (fun opcode => existT _ (labelCount opcode) (fetch_rule opcode)).
Definition faultHandler := FaultRoutine.faultHandler fetch_rule_withsig.

(* Bit more glue *)
Lemma handler_correct : 
  forall m i s raddr c opcode vls pcl olr lpc,
  forall (INPUT: cache_hit c (opCodeToZ opcode) (labsToZs vls) (labToZ pcl))
         (RULE: apply_rule (fetch_rule opcode) vls pcl = Some (olr,lpc)), 
    exists c',
    runsToEscape (CState c m faultHandler i (CRet raddr false false::s) (0,handlerTag) true)
                 (CState c' m faultHandler i s raddr false) /\
    handler_final_mem_matches' olr lpc c c'.
Proof.
  intros.
  exploit (@handler_correct_succeed _ _ _ _ fetch_rule_withsig opcode); eauto.
Qed.  

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

Lemma match_stacks_args : forall args s cs,
   match_stacks (args ++ s) cs -> 
   exists args' cs', cs = args'++cs'
                      /\ match_stacks args args'
                      /\ match_stacks s cs'.
Proof.
  induction args; intros.
  simpl in *. exists nil; exists cs. split; eauto.
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

Lemma match_stacks_data : forall s cs,
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

Lemma match_stacks_app : forall s cs s' cs',
    match_stacks s cs ->
    match_stacks s' cs' ->
    match_stacks (s++s') (cs++cs').
Proof.
  induction 1 ; intros; (simpl; eauto).
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

Lemma c_pop_to_return_pops_data: forall cdstk a b p cs,   
     (forall a : CStkElmt, In a cdstk -> exists d : Atom, a = CData d) ->
     c_pop_to_return (cdstk ++ CRet a b p :: cs) (CRet a b p :: cs).
Proof.
  induction cdstk; intros.
  simpl; auto. constructor.
  simpl. destruct a.
  constructor. eapply IHcdstk; eauto.
  intros; (eapply H ; eauto ; constructor 2; auto).
  exploit (H (CRet a b0 b1)); eauto.
  constructor; auto.
  intros [d Hcont]. inv Hcont.
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
  assert (Hcdstk:= match_stacks_data Hmatch H0); eauto.
  eapply c_pop_to_return_pops_data; eauto.
Qed.
          
Definition cache_up2date tmuc :=
  forall opcode vls pcl,
    cache_hit tmuc (opCodeToZ opcode) (labsToZs vls) (labToZ pcl) ->
    match apply_rule (fetch_rule opcode) vls pcl with
      | Some (Some l, rpcl) => cache_hit_read tmuc (labToZ l) (labToZ rpcl)
      | Some (None, rpcl) => exists t', cache_hit_read tmuc t' (labToZ rpcl)
      | None => False
    end.

Definition cache_up2date_weak tmuc :=
  forall opcode vls pcl rl rpcl,
  forall (RULE: apply_rule (fetch_rule opcode) vls pcl = Some (rl, rpcl)),
  forall (CHIT: cache_hit tmuc (opCodeToZ opcode) (labsToZs vls) (labToZ pcl)),
    match rl with 
        | Some l => cache_hit_read tmuc (labToZ l) (labToZ rpcl)
        | None => exists t', cache_hit_read tmuc t' (labToZ rpcl)
    end.

Lemma cache_up2date_success :
  forall tmuc, cache_up2date tmuc -> cache_up2date_weak tmuc.
Proof.
  unfold cache_up2date, cache_up2date_weak.
  intros.
  specialize (H opcode vls pcl CHIT).
  rewrite RULE in H.
  trivial.
Qed.

Inductive match_states : @AS L -> CS -> Prop :=
 ms: forall am cm i astk tmuc cstk apc cpc
              (CACHE: cache_up2date tmuc)
              (STKS: match_stacks astk cstk)
              (MEM: cm = mem_labToZ am)
              (PC: cpc = atom_labToZ apc),
         match_states (AState am i astk apc)
                      (CState tmuc cm faultHandler i cstk cpc false).


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

           
Lemma handler_cache_hit_read_some: 
  forall rl m rpcl tmuc,
    handler_final_mem_matches' (Some rl) rpcl m tmuc ->
    cache_hit_read tmuc (labToZ rl) (labToZ rpcl). 
Proof.
  intros; inv H ; auto.
Qed.

Lemma handler_cache_hit_read_none: 
  forall m rpcl tmuc,
    handler_final_mem_matches' None rpcl m tmuc ->
    exists t, cache_hit_read tmuc t (labToZ rpcl). 
Proof.
  intros; inv H ; auto.
Qed.

Ltac allinv' :=
  allinv ; 
    (match goal with 
       | [ H1:  ?f _ _ = _ , 
           H2:  ?f _ _ = _ |- _ ] => rewrite H1 in H2 ; inv H2
     end).

Definition optionlabToZ (ol: option L) : Z := 
      match ol with 
          | None => labToZ bot
          | Some l => labToZ l
      end.

Lemma handler_final_cache_hit_preserved: 
  forall tmuc tmuc' rl opcode labs rpcl pcl,
    handler_final_mem_matches' rl rpcl tmuc tmuc' ->
    cache_hit tmuc  opcode labs pcl ->
    cache_hit tmuc' opcode labs pcl.
Proof. 
  intros until 0. intros Hfinal HCHIT. inv HCHIT.
  inv Hfinal. unfold update_cache_spec_rvec in *. 
  assert (exists tagr tagrpc, cache_hit_read tmuc' tagr tagrpc).
    destruct rl.
      eexists; eexists; eauto.
      destruct H as [tagr0 Q]. eexists; eexists; eauto. 
  destruct H1 as [tagr' [tagrpc' C]]. 
  inv C. 
  repeat (match goal with
    | [ HTAG : tag_in_mem _ ?addr _ |- _ ] => inv HTAG
  end).
  econstructor; econstructor;
  try (rewrite <- H0; eauto;
       match goal with 
        | [ |- ?a <> ?b ] => try (unfold a, b ; congruence)
       end; fail); eauto.
Qed.

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
    nth_labToZ (Vector.cons L a n v) (S nth) 
    = nth_labToZ v nth.
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
  try solve [eapply handler_cache_hit_read_none; eauto
            |eapply handler_cache_hit_read_some; eauto].

Lemma match_observe: 
  forall s1 s2,
    match_states s1 s2 ->
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
    | [ Hrule : run_tmr ?opcode ?v ?pcl = Some (?rl, ?rpcl) |- _ ]  => 
      set (tags := labsToZs v);
      set (op := opCodeToZ opcode);
      set (pct := labToZ pcl);
      set (rpct := labToZ rpcl);
      match rl with 
        | Some ?rll => set (rt := labToZ rll)
        | _ => idtac
      end
  end; 
  match goal with 
    | [ HH: match_states (AState ?m _ _ _) _ |- _ ] => set (cm := mem_labToZ m)
  end.

Ltac solve_read_m :=
  (unfold nth_labToZ; simpl);
  (unfold Vector.nth_order; simpl);
  (eapply read_m_labToZ; eauto).

Ltac res_label :=
  match goal with 
    | [Hrule: apply_rule _ _ _ = Some (?rl,_) |- _ ] =>
      destruct rl; 
        try (solve [inv Hrule])
  end; 
  try match goal with 
    | [Hrule: apply_rule _ _ _ = Some (None,_), 
       Hcache : cache_up2date_weak _ , 
       CHIT : cache_hit _ _ _ _ |- _ ] =>
      let ASSERT := fresh "Assert" in 
      let LL := fresh "ll" in 
      let HLL := fresh "Hll" in 
      assert (ASSERT := Hcache _ _ _ _ _ Hrule CHIT); eauto; 
      simpl in ASSERT; 
      destruct ASSERT as [LL HLL]
      end.

Ltac build_cache_and_tmu := 
  simpl; 
  match goal with 
    | [Hmiss: ~ cache_hit _ ?op ?tags ?pct , 
       Hrule: apply_rule _ _ _ = Some _ ,
       i : list Instr 
     |- context[ (CState _ ?cm _ _ ?cstk (?pcv,_) _) ] ] =>
      let CHIT := fresh "CHIT" in 
      set (tmuc':= build_cache op tags pct);
      assert (CHIT : cache_hit tmuc' op tags pct) 
        by (eauto using build_cache_hit); 
      edestruct (handler_correct cm i cstk (pcv,pct) _ _ CHIT Hrule) as [c [Hruns Hmfinal]];
      eauto
  end.

Hint Resolve match_stacks_app match_stacks_data match_stacks_length.

Definition op_cons_ZToLab (oe: option Event) (t: list CEvent) := 
  match oe with 
    | Some (EInt e) => (CEInt (atom_labToZ e))::t
    | None => t
  end.

Lemma op_cons_ZToLab_none : (op_cons_ZToLab None nil) = (op_cons None (@nil CEvent)).
Proof. reflexivity. Qed.

Ltac hint_event := rewrite op_cons_ZToLab_none.

Ltac priv_steps :=
  match goal with
    | [Hruns : runsToEscape ?s ?s',
       Hmfinal: handler_final_mem_matches' _ _ _ _ |- _ ] =>
      (eapply runsToEscape_plus in Hruns; [| congruence]);
        let ll := fresh "ll" in
        let Hll := fresh "Hll" in
        let Hspec := fresh "Hspec" in
      (generalize Hmfinal; intros [[ll Hll] Hspec]);
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
              (eapply plus_right with (s2:= s') (t:= nil) (e:= None); eauto);
              (econstructor; eauto)                                               
          end
  end.

Lemma step_preserved: 
  forall s1 s1' e s2,
    step_rules s1 e s1' ->
    match_states s1 s2 ->
    (exists s2', plus cstep s2 (op_cons_ZToLab e nil) s2' /\ match_states s1' s2').
Proof.
  intros s1 s1' e s2 Hstep Hmatch. inv Hstep; try renaming;
    match goal with 
      | [Htmr : run_tmr _ _ _ = _ ,
         Hmatch : match_states _ _ |- _ ] => 
          inv Hmatch ; 
          unfold run_tmr in Htmr
    end;
    generalize (cache_up2date_success CACHE);
    intros CACHE'.

  - Case "Noop".    
    destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
    + exists (CState tmuc cm faultHandler i cstk (pcv+1, pct) false).
      res_label. subst pct. 
      split; inv H0; eauto.
      hint_event. eapply plus_step; eauto. eapply cstep_nop ; eauto. 
     
    + build_cache_and_tmu. res_label.
      exists (CState c cm faultHandler i cstk (pcv+1, rpct) false). split.
      * priv_steps.
        eapply handler_final_cache_hit_preserved; eauto.
      * econstructor ; eauto. 
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
   + build_cache_and_tmu.  
     exists (CState c cm faultHandler i ((CData (x1v+x2v,rt))::cs0) (pcv+1, rpct) false). 
     split.
     * priv_steps.        
       eapply handler_final_cache_hit_preserved; eauto.
       eapply handler_cache_hit_read_some; eauto.            
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
   + build_cache_and_tmu. 
     exists (CState c cm faultHandler i ((x1v-x2v,rt):::cs0) (pcv+1, rpct) false). 
     split.
     * simpl in Hruns. priv_steps. 
       eapply handler_final_cache_hit_preserved; eauto.
       eapply handler_cache_hit_read_some; eauto.            
     * econstructor ; eauto. 
       inv_cache_update.

- Case "Push ". 
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
   + exists (CState tmuc cm faultHandler i ((cv,rt):::cstk) (pcv+1,rpct) false).
     split. 
     * eapply plus_step ; eauto. eapply cstep_push ; eauto. 
       eapply CACHE' with (1:= H0); eauto. auto.
     * eauto.         
   + build_cache_and_tmu. 
     exists (CState c cm faultHandler i ((cv,rt):::cstk) (pcv+1, rpct) false). split.
     * simpl in Hruns. priv_steps. 
       eapply handler_final_cache_hit_preserved; eauto.
       eapply handler_cache_hit_read_some; eauto.            
     * econstructor ; eauto. 
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
   + build_cache_and_tmu. 
     exists (CState c cm faultHandler i ((xv,rt):::cs) (pcv+1, rpct) false). split.
     * simpl in Hruns. simpl. 
       priv_steps.
       eapply handler_final_cache_hit_preserved; eauto.
       eapply handler_cache_hit_read_some; eauto.            
       solve_read_m.
       auto.
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
     * priv_steps.
       eapply handler_final_cache_hit_preserved; eauto.
       eapply handler_cache_hit_read_some; eauto.            
       solve_read_m. auto.
     * econstructor ; eauto. 
       inv_cache_update.

- Case " Jump ". 
  inv STKS. 
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].  
   + exists (CState tmuc cm faultHandler i cs (pcv',rpct) false).
     split. 
     * eapply plus_step ; eauto. simpl. 
       res_label. eapply cstep_jump  ; eauto. auto.
     * econstructor; eauto.
   + build_cache_and_tmu. res_label.
     exists (CState c cm faultHandler i cs (pcv', rpct) false). split.
     * priv_steps.
       eapply handler_final_cache_hit_preserved; eauto.
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
   + build_cache_and_tmu. res_label.
     exists (CState c cm faultHandler i cs 
                    (if 0 =? 0 then pcv+1 else pcv+offv , rpct) false). 
     split.
     * res_label. 
       priv_steps.
       eapply handler_final_cache_hit_preserved; eauto.
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
       eapply handler_final_cache_hit_preserved; eauto.
     * econstructor ; eauto. 
       inv_cache_update.
       case_eq (av =? 0)%Z; intros; auto.
       eelim H1; eauto.
       rewrite Z.eqb_eq in H2. auto.
       
- Case " Call ". 
  inv STKS.        
  edestruct (match_stacks_args _ _ H4) as [args' [cs' [Heq [Hargs Hcs]]]]; eauto.
  inv Heq.  
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].  
   + exists (CState tmuc cm faultHandler i 
                    (args'++ (CRet (pcv+1, rt) r false)::cs') (pcv',rpct) false).
     split. 
     * eapply plus_step ; eauto. 
       eapply cstep_call ; eauto. 
       eapply CACHE' with (1:= H0); eauto. auto.
     * econstructor; eauto. 
   + build_cache_and_tmu. 
     exists (CState c cm faultHandler i 
                    (args'++ (CRet (pcv+1, rt) r false)::cs') (pcv',rpct) false). 
     split. 
     * priv_steps.
       eapply handler_final_cache_hit_preserved; eauto.
       eapply handler_cache_hit_read_some; eauto.                   
     * econstructor ; eauto. 
       inv_cache_update.

- Case " Ret ".  
  exploit @pop_to_return_spec; eauto.
  intros [dstk [stk [a [b [Heq Hdata]]]]]. inv Heq.
  exploit @pop_to_return_spec2; eauto. intros Heq. inv Heq.
  exploit @pop_to_return_spec3; eauto. intros Heq. inv Heq.
  
  edestruct (match_stacks_args _ _ STKS) as [args' [cs' [Heq [Hargs Hcs]]]]; eauto.
  inv Heq. inv Hcs. simpl atom_labToZ in *.

  exploit match_stacks_pop_to_return; eauto. 
  erewrite match_stacks_length; auto.
  intros.
     
  destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].  
  + exists (CState tmuc cm faultHandler i cs (pcv',rpct) false).
     split. 
     * res_label. eapply plus_step ; eauto. 
     * econstructor; eauto. 
       
   + build_cache_and_tmu. 
     exists (CState c cm faultHandler i cs (pcv',rpct) false). res_label. 
     split.
     * priv_steps.
       eapply handler_final_cache_hit_preserved; eauto.
     * econstructor ; eauto. 
       inv_cache_update.

- Case " VRet ".
  inv STKS.
  exploit @pop_to_return_spec; eauto.
  intros [dstk [stk [a [b [Heq Hdata]]]]]. inv Heq.
  exploit @pop_to_return_spec2; eauto. intros Heq. inv Heq.
  exploit @pop_to_return_spec3; eauto. intros Heq. inv Heq.
  edestruct (match_stacks_args _ _ H4) as [args' [cs' [Heq [Hargs Hcs]]]]; eauto.
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
       (generalize Hmfinal; intros [[ll Hll] Hspec]);
       (simpl atom_labToZ).       
       (eapply plus_trans with (s2:= (CState tmuc' (mem_labToZ m) faultHandler i
                                             (CRet (pcv, pct) false false
                                                   :: (resv, labToZ resl)
                                                   ::: args' ++ CRet (pcv', labToZ pcl') true false :: cs)
                                             (0, handlerTag) true)); eauto).
       eapply plus_right ; eauto.
       eapply cstep_vret; eauto.
       eapply handler_final_cache_hit_preserved; eauto.
       eapply handler_cache_hit_read_some; eauto. auto.
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
       (generalize Hmfinal; intros [[ll Hll] Hspec]);
       (simpl atom_labToZ).       
       (eapply plus_trans ; eauto). 
       eapply plus_right ; eauto.
       eapply cstep_out; eauto.
       eapply handler_final_cache_hit_preserved; eauto.
       eapply handler_cache_hit_read_some; eauto.
       simpl. 
       replace ll with (labToZ rl). auto.
       exploit handler_cache_hit_read_some; eauto. 
       intros. inv H1. 
       inv TAG_Res. inv TAG_Res0. allinv'. auto. 
     * econstructor ; eauto. 
       inv_cache_update.
Qed.
  
Lemma step_preserved_observ: 
  forall s1 e s1' s2,
    step_rules s1 e s1' ->
    match_states s1 s2 ->
    s1 = observe_cstate s2 /\ (exists s2', plus cstep s2 (op_cons_ZToLab e nil) s2' /\ match_states s1' s2').
Proof.
  intros.
  split. 
  apply match_observe; auto.
  eapply step_preserved; eauto.
Qed.

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
  
Require Import LNIwithEvents.

(* Let aexec_with_trace := sys_trace step_rules success (fun x => x). *)
(* Let cexec_with_trace := sys_trace cstep c_success observe_cstate. *)

(* The fwd simulation is not a lockstep diagram anymore *)
(* Theorem refinement: forall s1 s2 T,  *)
(*                       match_states s1 s2 -> *)
(*                       cexec_with_trace s2 T -> *)
(*                       aexec_with_trace s1 T.  *)
(* Proof. *)
(*   eapply forward_backward_sim; eauto. *)
(*   exact step_preserved_observ. *)
(*   exact succ_preserved. *)
(*   exact cmach_determ. *)
(* Qed.   *)

End Refinement.
