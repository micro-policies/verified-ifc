Require Import Relations.
Require Import EqNat.
Require Import ZArith.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Utils Lattices CLattices WfCLattices.

Require Import TMUInstr.
Require Import Abstract Rules AbstractMachine.

Require Import Concrete ConcreteMachineSmallStep CodeGen CodeSpecs.
Require Import FaultRoutine.
Require Import Determinism.

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
Lemma our_handler_correct_succeed : 
  forall m i s raddr c opcode vls pcl olr lpc,
  forall (INPUT: cache_hit c (opCodeToZ opcode) (labsToZs vls) (labToZ pcl))
         (RULE: apply_rule (fetch_rule opcode) vls pcl = Some (olr,lpc)), 
    exists c',
    runsToEscape (CState c m faultHandler i (CRet raddr false false::s) (0,handlerTag) true)
                 (CState c' m faultHandler i s raddr false) /\
    handler_final_mem_matches' olr lpc c c'.
Proof.
  intros.
  exploit (@handler_correct_succeed _ _ _ fetch_rule_withsig opcode); eauto.
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

Definition cache_up2date tmuc :=
  forall opcode vls pcl rl rpcl,
  forall (RULE: apply_rule (fetch_rule opcode) vls pcl = Some (rl, rpcl)),
  forall (CHIT: cache_hit tmuc (opCodeToZ opcode) (labsToZs vls) (labToZ pcl)),
    match rl with 
        | Some l => cache_hit_read tmuc (labToZ l) (labToZ rpcl)
        | None => exists t', cache_hit_read tmuc t' (labToZ rpcl)
    end.

Inductive match_states : @AS L -> CS -> Prop :=
 ms: forall am cm i astk tmuc cstk apc cpc
              (CACHE: cache_up2date tmuc)
              (STKS: match_stacks astk cstk)
              (MEM: cm = mem_labToZ am)
              (PC: cpc = atom_labToZ apc),
         match_states (AState am i astk apc)
                      (CState tmuc cm faultHandler i cstk cpc false).

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

(** Observing a concete cache is just projecting it a the abstract level *)
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
  inv Hfinal. unfold update_cache_spec_rvec in *. clear H.
  econstructor;
  constructor;
  match goal with 
    | [HTAG: tag_in_mem _ ?addr _
       |- read_m ?addr _ = Some _  ] => 
      (rewrite <- H0 ; eauto); 
      (inv HTAG; eauto);
      (match goal with 
         | [ |- ?a <> ?b ] => try (unfold a, b ; congruence)
       end)
   end.
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

Ltac res_label :=
  match goal with 
    | [Hrule: apply_rule _ _ _ = Some (?rl,_) |- _ ] =>
      destruct rl; 
        try (solve [inv Hrule])
  end.
 
Ltac inv_cache_update :=
  unfold cache_up2date; intros; 
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
   allinv'; 
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

Hint Constructors star.

Lemma runsToEscape_star: forall s1 s2, 
 runsToEscape s1 s2 ->
 star cstep s1 s2.
Proof.
  induction 1 ; intros; auto.
Qed.

Lemma star_right : forall S (Rstep: relation S) s1 s2, 
                     star Rstep s1 s2 -> 
                     forall s3, 
                       Rstep s2 s3 -> star Rstep s1 s3.
Proof.
  induction 1; intros.
  eapply star_step; eauto.
  eauto.
Qed.

Ltac priv_steps := 
  match goal with 
    | [Hstar : runsToEscape ?s1 ?s2, 
               Hfinal: handler_final_mem_matches' _ _ _ _ |- _ ] =>
      (eapply runsToEscape_star in Hstar; eauto);
      (generalize Hfinal; intros [[ll Hll] Hspec]);
      (simpl); 
      (apply star_step with s1; eauto); 
      (eapply star_right with s2; eauto)
  end.

Lemma step_preserved: 
  forall s1 s1' s2,
    step_rules s1 s1' ->
    match_states s1 s2 ->
    (exists s2', star cstep s2 s2' /\ match_states s1' s2').
Proof.
  intros s1 s1' s2 Hstep Hmatch. inv Hstep. inv Hmatch.
  - Case "Noop".
  { set (tags := labsToZs (<||>: Vector.t L _)). 
    set (op := opCodeToZ OpNoop).
    set (pct := labToZ pcl). 
    set (rpct := labToZ rpcl). 
    set (cm := mem_labToZ m). 
    unfold run_tmr in H0.
    destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
    + exists (CState tmuc cm faultHandler i cstk (pcv+1, pct) false).
      res_label. split.
      unfold cache_up2date in CACHE. 
      assert (exists t' : Z, cache_hit_read tmuc t' rpct) by (eapply CACHE with (1:= H0); eauto). 
      destruct H1 as [ll Hll].
      subst pct. inv H0. eapply star_step; eauto. eapply cstep_nop with (rl:= ll) ; eauto. 
      subst pct. inv H0; eauto. 

     + set (tmuc':= build_cache op tags pct).  
       assert (CHIT' : cache_hit tmuc' op tags pct) by (eauto using build_cache_hit). 
       edestruct (@our_handler_correct_succeed cm i cstk (pcv,pct) tmuc') as [c [Hruns Hmfinal]]; 
         [exact CHIT' | exact H0 |].  (* ARGH: eauto should work *)
       res_label.
       exists (CState c cm faultHandler i cstk (pcv+1, rpct) false). split.
          * priv_steps.
            eapply cstep_nop; eauto.
            eapply handler_final_cache_hit_preserved; eauto.
          * econstructor ; eauto. 
            inv_cache_update. 
    }
 - Case "Add".
  { set (tags := labsToZs (<|x1l; x2l |>)). 
    set (op := opCodeToZ OpAdd). 
    set (pct := labToZ pcl). 
    set (rt := labToZ rl). 
    set (rpct := labToZ rpcl). 
    set (cm := mem_labToZ m). 
    unfold run_tmr in H0. inv Hmatch.
      destruct (classic (cache_hit tmuc op tags pct)) as [CHIT | CMISS].
      + inv STKS. inv H3.
        exists (CState tmuc cm faultHandler i ((CData (x1v+x2v,rt))::cs0) (pcv+1, rpct) false).
        split; eauto.
        unfold cache_up2date in CACHE. 
        eapply star_step ; eauto. eapply cstep_add ; eauto.        
        eapply CACHE with (1:= H0); eauto.
        
     + set (tmuc':= build_cache op tags pct). 
       assert (CHIT' : cache_hit tmuc' op tags pct)
         by (eauto using build_cache_hit).
       edestruct (@our_handler_correct_succeed cm i cstk (pcv,pct) tmuc') as [c [Hruns Hmfinal]].
       exact CHIT'. eauto.
       inv STKS. inv H3. 
       exists (CState c cm faultHandler i ((CData (x1v+x2v,rt))::cs0) (pcv+1, rpct) false). split.
          * simpl in Hruns. priv_steps. 
            eapply cstep_add ; eauto.                
            eapply handler_final_cache_hit_preserved; eauto.
            eapply handler_cache_hit_read_some; eauto.            
          * econstructor ; eauto. 
            inv_cache_update.
}
Admitted.

Lemma step_preserved_observ: 
  forall s1 s1' s2,
    step_rules s1 s1' ->
    match_states s1 s2 ->
    s1 = observe_cstate s2 /\ (exists s2', star cstep s2 s2' /\ match_states s1' s2').
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

Let aexec_with_trace := sys_trace step_rules success (fun x => x).
Let cexec_with_trace := sys_trace cstep c_success observe_cstate.

(* The fwd simulation is not a lockstep diagram anymore *)
(* Theorem refinement: forall s1 s2 T,  *)
(*                       match_states s1 s2 -> *)
(*                       cexec_with_trace s2 T -> *)
(*                       aexec_with_trace s1 T.  *)
(* Proof. *)
(*   eapply forward_backward_sim; eauto. *)
(*   admit.  *)
(*   exact step_preserved_observ. *)
(*   exact succ_preserved. *)
(*   exact cmach_determ. *)
(* Qed.   *)

End Refinement.


  
