Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.
Require Import Concrete.

Set Implicit Arguments.
Local Open Scope Z_scope.

(* Require Import Coq.Unicode.Utf8.  *)

Section CMach.


Notation "i @ pc # instr" := (index_list_Z pc i = Some instr) (no associativity, at level 55).
Notation "'__'" := dontCare.
 
(** The concrete machine in privileged mode. *)
Inductive cstep_p :  CS -> CS -> Prop := 
| cp_nop : forall c m fh i s pcv pcl,
    fh @ pcv # Noop ->
    cstep_p (CState c m fh i s (pcv,pcl) true) (CState c m fh i s (pcv+1,pcl) true)

| cp_add: forall c m fh i s pcv pcl x1v x1l x2v x2l, 
    fh @ pcv # Add ->
    cstep_p (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true)  
            (CState c m fh i ((x1v+x2v,handlerTag):::s) (pcv+1,pcl) true)

| cp_sub: forall c m fh i s pcv pcl x1v x1l x2v x2l, 
    fh @ pcv # Sub ->
    cstep_p (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true) 
            (CState c m fh i ((x1v-x2v,handlerTag):::s) (pcv+1,pcl) true)

| cp_push: forall c m fh i s pcv pcl cv, 
    fh @ pcv # Push cv ->
    cstep_p (CState c m fh i s (pcv,pcl) true) 
            (CState c m fh i ((cv,handlerTag):::s) (pcv+1,pcl) true)

| cp_load: forall c m fh i s pcv pcl addrv addrl xv xl,
    fh @ pcv # Load ->
    read_m addrv c = Some (xv,xl) ->
    cstep_p (CState c m fh i ((addrv,addrl):::s) (pcv,pcl) true) 
            (CState c m fh i ((xv,handlerTag):::s) (pcv+1,pcl) true)

| cp_store: forall c m fh i s pcv pcl c' addrv addrl x, 
    fh @ pcv # Store ->
    upd_m addrv x c = Some c' ->
    cstep_p (CState c m fh i ((addrv,addrl)::: x :::s) (pcv,pcl) true)
            (CState c' m fh i s (pcv+1,pcl) true)

| cp_jump: forall c m fh i s pcv pcl pcj pcjl,
    fh @ pcv # Jump ->
    cstep_p (CState c m fh i ((pcj,pcjl):::s) (pcv,pcl) true) 
            (CState c m fh i s (pcj,pcjl) true)

| cp_branchnz: forall c m fh i s pcv pcl offv av al,
    fh @ pcv # BranchNZ offv -> 
    cstep_p (CState c m fh i ((av,al):::s) (pcv,pcl) true) 
            (CState c m fh i s (if av =? 0 then pcv+1 else pcv+offv, handlerTag) true)

| cp_call: forall c m fh i s pcv pcl a r args pcc pccl,
    fh @ pcv # Call a r -> 
    length args = a -> (forall a, In a args -> exists d, a = CData d) ->
    cstep_p (CState c m fh i ((pcc,pccl):::args++s) (pcv,pcl) true) 
            (CState c m fh i (args++(CRet (pcv+1, pcl) r true)::s) (pcc, pccl) true)

| cp_ret: forall c m fh i s pcv pcl  pcret pcretl s' pret, 
    fh @ pcv # Ret -> (* can either return to user/priv mode *)
    c_pop_to_return s ((CRet (pcret,pcretl) false pret)::s') ->
    cstep_p (CState c m fh i s  (pcv,pcl) true) 
            (CState c m fh i s' (pcret,pcretl) pret)

| cp_vret: forall c m fh i s pcv pcl s' pcret pcretl resv resl, 
    fh @ pcv # VRet -> (* cannot vreturn to user mode *)
    c_pop_to_return s ((CRet (pcret,pcretl) true true)::s') ->
    cstep_p (CState c m fh i ((resv,resl):::s) (pcv,pcl) true) 
            (CState c m fh i ((resv,resl):::s') (pcret, pcretl) true).


(** TMU. If rule is in the cache (currently just a single entry),
   leave the state unchanged and return
   Some(result_tag,result_pc_tag); otherwise, set the state to invoke
   the TMU fault handler code and return None.  *)



(* [check_stags opc oplabs pcl s1 s2] holds when: either [s2]
has an up to date cache or [s2] is the privileged state in which the
tmu routine must then be executed *)
Inductive check_tags (opcode: Z) (tags: Z * Z * Z) (pctag:Z): CS -> CS -> Prop :=
| ct_upriv_chit : (* m vector is in the cache *)
    forall c m fh i s pc,
    forall (CHIT: cache_hit c opcode tags pctag),      
      check_tags opcode tags pctag 
                 (CState c m fh i s pc false) (CState c m fh i s pc false)
| ct_upriv_cmiss: (* not in cache: arrange to enter TMU fault handler *)
    forall c m fh i s pc,
      forall (CMISS: ~ cache_hit c opcode tags pctag),
    check_tags opcode tags pctag 
               (CState c m fh i s pc false) 
               (CState (build_cache opcode tags pctag) m fh i ((CRet pc false false)::s) (0,handlerTag) true).

(* New version decoupled from runsToEnd  *)

(** Reflexive transitive closure. *)
Inductive star (S: Type) (Rstep: S -> S -> Prop): S -> S -> Prop :=
  | star_refl: forall s,
      star Rstep s s
  | star_step: forall s1 s2 s3,
      Rstep s1 s2 -> star Rstep s2 s3 -> 
      star Rstep s1 s3.

Inductive runsToEscape : CS -> CS -> Prop :=
| rte_success: (* executing until a return to user mode *)
    forall cs cs',
    forall (PRIV:  priv cs = true)
           (STAR:  star cstep_p cs cs')
           (UPRIV: priv cs' = false), 
      runsToEscape cs cs'
| rte_fail : (* executing the tmu until it fails at a neg. pc in priv mode *)
    forall cs cs',
    forall (PRIV: priv cs = true)
           (STAR: star cstep_p cs cs')
           (PRIV: priv cs' = true)
           (FAIL: fst (pc cs') < 0), 
      runsToEscape cs cs'
| rte_upriv: (* in unpriv. mode, it already escaped *) 
    forall cs,
    forall (UPRIV: priv cs = false),
      runsToEscape cs cs.


(* [run_tmu] checks the tags, and potentially execute all the code of
   the tmu fault handler and goes back to the unprivileged mode.  We
   check it does not fail by going ruling out pc (-1,handlerTag) or
   demanding priv. bit of resulting state to be false.  If the fault
   handler fails, the concrete machine just does not step *) 
Inductive run_tmu (opcode: OpCode) (t1 t2 t3: Z) (pct:Z) (cs: CS) : CS -> Prop :=
| rtmu_upriv : forall cs' c m s ppc fh i,
      priv cs = false ->
      (* DD: Not sure we need this: (pc cs = ppc) *)
      check_tags (opCodeToZ opcode) (t1,t2,t3) pct cs cs' ->
      runsToEscape cs' (CState c m fh i s ppc false) ->
      run_tmu opcode t1 t2 t3 pct cs (CState c m fh i s ppc false).

(* TODO DD: MAYBE RUNS_TO_ESCAPE ONLY IF CHECK_TAG *)

(** Concrete machine transition relation. Unprivileged mode. *)
(* APT: All these p,p' are superflous. *)
Inductive cstep : CS -> CS -> Prop := 
| cstep_nop : forall c m fh i s pcv pcl rl rpcl p c' m' pcv' pcl' p' fh' i' s',
    i @ pcv # Noop ->
    run_tmu OpNoop __ __ __  pcl 
(* APT:  OpNoop bot bot bot pcl *)
            (CState c m fh i s (pcv,pcl) p) 
            (CState c' m' fh' i' s' (pcv',pcl') p') ->
    cache_hit_read c' rl rpcl -> 
    cstep (CState c m fh i s (pcv,pcl) p) (CState c' m' fh' i' s' (pcv+1,rpcl) p')

| cstep_add: forall c c' fh fh' m i s rpcl pcv  pcl p rl x1v x1v' x1l x1l' x2v  x2v',
               forall x2l x2l' pcv' pcl' m' p' i' s', 
    i @ pcv # Add ->
    run_tmu OpAdd x1l x2l __ pcl 
            (CState c  m  fh  i  ((x1v,x1l):::(x2v,x2l):::s)      (pcv,pcl)   p) 
            (CState c' m' fh' i' ((x1v',x1l'):::(x2v',x2l'):::s') (pcv',pcl') p') ->
    cache_hit_read c' rl rpcl -> 
    cstep (CState c  m  fh  i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)     p )  
          (CState c' m' fh' i ((x1v'+x2v',rl):::s')       (pcv'+1,rpcl) p')

| cstep_sub: forall c c' fh fh' m i s pcv pcl rpcl p rl x1v x1v' x1l m' x1l' x2v,
             forall x2v' x2l x2l' pcv' pcl' p' i' s', 
    i @ pcv # Sub ->
    run_tmu OpSub x1l x2l __  pcl 
            (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) p)
            (CState c' m' fh' i' ((x1v',x1l'):::(x2v',x2l'):::s') (pcv',pcl') p') ->    
    cache_hit_read c' rl rpcl -> 
    cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) p) 
          (CState c' m' fh' i' ((x1v'-x2v',rl):::s') (pcv'+1,rpcl) p')

| cstep_push: forall c fh c' fh' m i s cv pcv pcl rpcl p rl m' i' s' p' pcv' pcl', 
    i @ pcv # Push cv ->
    run_tmu OpPush __ __ __ pcl 
            (CState c  m fh i s (pcv,pcl) p)
            (CState c' m' fh' i' s' (pcv',pcl') p') ->  
    cache_hit_read c' rl rpcl ->     
    cstep (CState c m fh i s (pcv,pcl) p) (CState c' m' fh' i' ((cv,0%Z):::s') (pcv'+1,rpcl) p')

| cstep_load: forall c c' fh fh' m i s pcv pcl addrv addrl xv xl rl rpcl p m' p' s' i',
              forall addrv' addrl' xv' xl' pcl' pcv', 
    i @ pcv # Load ->
    read_m addrv m = Some (xv,xl) ->
    run_tmu OpLoad addrl xl __ pcl 
            (CState c m fh i ((addrv,addrl):::s) (pcv,pcl) p) 
            (CState c' m' fh' i' ((addrv',addrl'):::s') (pcv',pcl') p') ->    
    read_m addrv' m' = Some (xv',xl') ->
    cache_hit_read c' rl rpcl ->     
    cstep (CState c m fh i ((addrv,addrl):::s) (pcv,pcl) p) 
          (CState c' m' fh' i' ((xv, rl):::s') (pcv'+1,rpcl) p')

| cstep_store: forall c c' fh fh' m i i' s pcv pcv' pcl pcl' addrv addrl addrv' addrl',
               forall xv xl xv' xl' mv ml mv' ml' rpcl rl p m' m'' s' p', 
    i @ pcv # Store ->
    read_m addrv m = Some (mv,ml) ->
    run_tmu OpStore addrl xl ml pcl 
            (CState c m fh i ((addrv,addrl):::(xv,xl):::s) (pcv,pcl) p) 
            (CState c' m' fh' i' ((addrv',addrl'):::(xv',xl'):::s') (pcv',pcl') p') ->    
    cache_hit_read c' rl rpcl ->     
    read_m addrv' m' = Some (mv',ml') ->
    upd_m addrv' (xv', rl) m' = Some m'' ->
    cstep (CState c m fh i ((addrv,addrl):::(xv,xl):::s) (pcv,pcl) p) 
          (CState c' m'' fh' i' s' (pcv'+1,rpcl) p')

| cstep_jump: forall c c' fh fh' m i i' s pcv pcl pcv' pcl' pcj pcjl rl rpcl m' p p' s' pcj' pcjl',
    i @ pcv # Jump ->
    run_tmu OpJump pcjl __ __ pcl 
            (CState c m fh i ((pcj,pcjl):::s) (pcv,pcl) p) 
            (CState c' m' fh' i' ((pcj',pcjl'):::s') (pcv',pcl') p') ->    
    cache_hit_read c' rl rpcl ->     
    cstep (CState c m fh i ((pcj,pcjl):::s) (pcv,pcl) p) 
          (CState c' m' fh' i' s' (pcj',rpcl) p')
               
| cstep_branchnz: forall c c' fh fh' m i i' s s' pcv pcl offv av al av' al' rl p rpcl p' m' pcv' pcl',
    i @ pcv # BranchNZ offv -> (* relative target *)
    run_tmu OpBranchNZ al __ __ pcl
            (CState c m fh i ((av,al):::s) (pcv,pcl) p)
            (CState c' m' fh' i' ((av',al'):::s') (pcv',pcl') p') ->    
    cache_hit_read c' rl rpcl ->     
    cstep (CState c m fh i ((av,al):::s) (pcv,pcl) p) 
          (CState c' m' fh' i' s' (if av' =? 0 then pcv'+1 else pcv'+offv, rpcl) p')

| cstep_call: forall c c' fh fh' m i s pcv pcl pcv' pcl' rl rpcl args a r p' i'
                     pcc pccl m' p s' pcc' pccl' args',
    i @ pcv # Call a r -> 
    length args = a -> (forall a, In a args -> exists d, a = CData d) ->
    length args' = a -> (forall a, In a args' -> exists d, a = CData d) ->
    run_tmu OpCall pccl __ __ pcl  (* APT: mod *)
            (CState c m fh i ((pcc,pccl):::args++s) (pcv,pcl) p) 
            (CState c' m' fh' i' ((pcc',pccl'):::args'++s') (pcv',pcl') p')  ->    
    cache_hit_read c' rl rpcl ->     
    cstep (CState c m fh i ((pcc,pccl):::args++s) (pcv,pcl) p) 
          (CState c' m' fh' i' (args'++(CRet (pcv'+1,(if p' then pcl' else rl)) r p')::s') 
                  (pcc', if p' then pccl' else rpcl) p')  (* APT: mod *)

| cstep_ret: forall c c' fh fh' m i s pcv pcl pcv' pcl' rl rpcl p' i' m' p s' 
                    pcret pcret' pcretl pcretl' s0 s0' pret pret', 
    i @ pcv # Ret -> 
    c_pop_to_return s ((CRet (pcret,pcretl) false pret)::s0) ->  (* APT: mod *)
    run_tmu OpRet pcretl __ __ pcl  (* APT: mod *)
            (CState c m fh i s (pcv,pcl) p)
            (CState c' m' fh' i' s' (pcv',pcl') p') ->    
    c_pop_to_return s' ((CRet (pcret',pcretl') false pret')::s0') ->
    cache_hit_read c' rl rpcl ->     
    cstep (CState c m fh i s (pcv,pcl) p) 
          (CState c' m' fh' i' s0' (pcret', if p' then pcretl' else rpcl) pret')

| cstep_vret: forall c c' fh fh' m i s pcv pcl pcv' pcl' rl rpcl p' i' m' p s' pcret pcret' 
                     pcretl pcretl' s0 s0' pret pret' resv resl resv' resl' , 
    i @ pcv # VRet -> 
    c_pop_to_return s ((CRet (pcret,pcretl) false pret)::s0) ->  (* APT: mod *)
    run_tmu OpVRet resl pcretl __ pcl   (* APT: mod *)
            (CState c m fh i ((resv,resl):::s) (pcv,pcl) p)
            (CState c' m' fh' i' ((resv',resl'):::s') (pcv',pcl') p') ->
    c_pop_to_return s' ((CRet (pcret',pcretl') true pret')::s0') ->
    cache_hit_read c' rl rpcl ->     
    cstep (CState c m fh i ((resv,resl):::s) (pcv,pcl) p) 
          (CState c' m' fh' i' ((resv',rl):::s0') (pcret', if p' then pcretl' else rpcl) pret')
.

(* Success is reaching a Halt state in non-privileged mode and valid address. *)
Definition c_success (cs : CS) : Prop :=
  match index_list_Z (fst (pc cs)) (imem cs) with
  | Some Halt => is_true (negb (priv cs))
  | _ => False
  end.



(* COMMENTING OUT THIS FOR NOW 

Lemma cons_not_same (A: Type): forall (s:list A) a, s = a::s -> False.
Proof.
  induction s ; congruence.
Qed.

Lemma c_pop_to_return_length: forall s s' , 
 @c_pop_to_return T s s' ->
 (length s' <= length s)%nat.
Proof.
  induction 1; intros; simpl; auto.
Qed.

Lemma cstep_p_non_loop : forall cs, ~ cstep_p cs cs.
Proof.
  intros. intro Hcont.
  inversion Hcont; try omega.
  eelim cons_not_same; eauto.
  eelim cons_not_same; eauto.

  generalize H; clear H. clear.
  generalize args s pcv pcl pcc pccl.
  induction args0; intros.
  simpl in *. congruence.
  simpl in *. inv H. eapply IHargs0; eauto.

  assert (~ c_pop_to_return s (CRet (pcv, pcl) false true :: s)).
  clear. intro Hcont'. 
  exploit @c_pop_to_return_length; eauto.
  intros. simpl in *. zify ; omega.
  congruence. 

  assert (~ c_pop_to_return s (CRet (pcv, pcl) true true :: s)).
  clear. intro Hcont'. 
  exploit @c_pop_to_return_length; eauto.
  intros. simpl in *. zify ; omega.
  congruence. 
Qed.  
Hint Resolve cstep_p_non_loop.
 *)

End CMach.

Hint Constructors check_tags run_tmu.

(*
(* New version particularized to cstep_p...  Don't think we
  need to be more general than that  *)
(* DEFINED MULTI_STEP TRANSITION IN PRIVILEGED MODE *)
Inductive runsToEscape : Z -> Z -> Z -> @CS T -> @CS T -> Prop :=
| rte_success: forall pc_start pc_end pc_fail cs cs' cs'',
               forall (PRIV: priv cs = true)
                      (TMU:  runsToEnd cstep_p pc_start pc_end cs cs')
                      (RET:  cstep_p cs' cs'') (* executing the return *)
                      (SUCC: priv cs'' = false), (* to user mode *)
                 runsToEscape pc_start pc_end pc_fail cs cs''
| rte_fail: forall pc_start pc_end pc_fail cs cs' cs'',
            forall (PRIV: priv cs = true)
                   (TMU:  runsToEnd cstep_p pc_start pc_fail cs cs')
                   (JMP:  cstep_p cs' cs''), (* executing jump -1 *)
                   (FAIL: handler_fails cs'') (* and being blocked in priv mode *)
              runsToEscape pc_start pc_end pc_fail cs cs''
| rte_upriv:forall pc_start pc_end pc_fail cs,
            forall (UPRIV: priv cs = false),
              runsToEscape pc_start pc_end pc_fail cs cs.
*)

(* DD: Not sure we need all that... *)
(* Ltac break_c_success_goal := *)
(*   match goal with *)
(*   | [|- context[c_success ?s]] => *)
(*       unfold c_success; *)
(*       match goal with *)
(*       | [|- context[index_list_Z ?idx ?imem]] => *)
(*          remember (index_list_Z idx imem) as oinstr; *)
(*          destruct oinstr as [i |]; try tauto; destruct i; try tauto *)
(*       end *)
(*   end. *)

(* Ltac break_c_success_hyp := *)
(*   match goal with *)
(*   | [H : c_success ?s |- _] => gdep H; break_c_success_goal; intro H *)
(*   end. *)

(* Ltac break_success := try break_success_goal; repeat break_success_hyp. *)

(* Lemma success_dec:  forall s, {success s} + {~success s}. *)
(* Proof. *)
(*  intro; break_success. *)
(*  unfold is_true.  destruct (negb (priv s) && (fst (pc s) >=? privInstSize)); intuition.  *)
(* Qed. *)

(* Easy lammas about the concrete *)
(* Lemma success_runSTO_None : forall  s s', *)
(*   success s -> *)
(*   ~ cstep s s'. *)
(* Proof. *)
(*   intros. break_success. intros Hcont;  inv Hcont; simpl in *; *)
(*   congruence. *)
(* Qed. *)