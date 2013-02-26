Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.
Require Import CLattices.
Require Import Concrete.

Set Implicit Arguments.
Local Open Scope Z_scope.

Section CMach.

Context {T: Type}
        {CLatt: ConcreteLattice T}.

Definition mvector (opcode: OpCode) (op1lab op2lab op3lab:option T) (pclab: T) : Z * Z * Z * Z * Z :=
   let optlabToZ optl :=
     match optl with
     | None => labToZ bot
     | Some l => labToZ l 
     end in
   (opCodeToZ opcode, optlabToZ op1lab, optlabToZ op2lab, optlabToZ op3lab, labToZ pclab).

Definition rvector (tagr:Z) (tagrpc:Z) : T * T :=
   (ZToLab tagr,ZToLab tagrpc). 

(* TMU action on each instruction.  If rule is in the cache (currently
just a single entry), leave the state unchanged and return
Some(result_tag,result_pc_tag); otherwise, set the state to invoke the
TMU fault handler code and return None. *)
 
(* [check_stags opc opl1 opl2 opl3 pcl s1 s2] holds when:
   - either [s2] has an up to date cache (or a cache that we don't care about) 
   - either [s2] is the privileged state in which the tmu routine should be executed *)
Inductive check_tags (opcode: OpCode) (opl1 opl2 opl3:option T) (pcl:T): @CS T -> @CS T -> Prop :=
| ct_priv : (* completely ignore cache (as in Haskell code) *)
    forall m i s pc, 
      check_tags opcode opl1 opl2 opl3 pcl 
                 (CState m i s pc true) (CState m i s pc true) 
                 
| ct_upriv_chit : (* m vector is in the cache *)
    forall m i s pc,
    forall (CHIT: cache_hit m (mvector opcode opl1 opl2 opl3 pcl)),      
      check_tags opcode opl1 opl2 opl3 pcl 
                 (CState m i s pc false) (CState m i s pc false)

| ct_upriv_cmiss: (* not in cache: arrange to enter TMU fault handler *)
    forall m i s pc m' mvec,
      forall (MVEC: mvec = (mvector opcode opl1 opl2 opl3 pcl))
             (CMISS: ~ cache_hit m mvec)
             (C_UPD: cache_hit m' mvec)
             (M_UPD: update_cache_spec_mvec m m'),
    check_tags opcode opl1 opl2 opl3 pcl 
               (CState m i s pc false) (CState m' i ((CRet pc false false)::s) (0,handlerLabel) true).

(* [run_tmu] checks the tags, and potentially execute all the code of the tmu fault handler 
   and goes back to the unprivileged mode. *)
Inductive run_tmu (Rstep: CS -> CS -> Prop) (opcode: OpCode) (opl1 opl2 opl3:option T) (pcl:T) (cs: CS) : @CS T -> Prop :=
| rtmu_upriv : 
    forall cs' m' s' p' pc' i',
      priv cs = false ->
      check_tags opcode opl1 opl2 opl3 pcl cs cs' ->
      runsToEscape Rstep 0 privInstSize cs' (CState m' i' s' pc' false) ->    
      (* and not failing by going to (-1,handlerLabel) or priv. bit of resulting state is false *)
      run_tmu Rstep opcode opl1 opl2 opl3 pcl cs (CState m' i' s' pc' p')
| rtmu_priv : 
    forall cs',
      priv cs = true ->
      check_tags opcode opl1 opl2 opl3 pcl cs cs' ->
      run_tmu Rstep opcode opl1 opl2 opl3 pcl cs cs'.

Inductive c_pop_to_return : list (@CStkElmt T) -> list (@CStkElmt T) -> Prop := 
| cptr_done: forall a b p s,
   c_pop_to_return ((CRet a b p)::s) ((CRet a b p)::s)
| cptr_pop: forall a s s',
    c_pop_to_return s s' ->
    c_pop_to_return ((CData a)::s) s'.

Lemma c_pop_to_return_ret : forall s1 s2,
  c_pop_to_return s1 s2 ->
  exists a b p s, s2 = (@CRet T a b p)::s.
Proof.
  induction 1; intros; simpl; eauto.
Qed.  
  
Lemma c_pop_to_return_spec : forall s1 s2,
  c_pop_to_return s1 s2 ->
  exists dstk, exists stk a b p,   
    s1 = dstk++(CRet a b p)::stk
    /\ (forall e, In e dstk -> exists a, e = CData a).
Proof.
  induction 1; intros; simpl in *. 
  exists nil ; exists s ; exists a ; exists b ; exists p.
  simpl ; split ; eauto.
  intuition.

  destruct IHc_pop_to_return as [dstk [stk [a0 [b0 [p0 [Hs Hdstk]]]]]].
  subst.
  exists ((CData a)::dstk).
  exists stk ; eauto.
  exists a0 ; exists b0 ; exists p0 ; split ; eauto.
  intros. inv H0.
  eauto.
  eapply Hdstk; auto.
 Qed.

Lemma c_pop_to_return_spec2: forall  s1 s2 p1 p2 b1 b2 a1 a2 dstk,
 c_pop_to_return (dstk ++ CRet a1 b1 p1 :: s2)
               (CRet a2 b2 p2 :: s1) ->
 (forall e : CStkElmt, In e dstk -> exists a : @Atom T, e = CData a) ->
 CRet a1 b1 p1 =  CRet a2 b2 p2.
Proof.
  induction dstk; intros.
  inv H. auto.
  simpl in *. 
  inv H. destruct (H0 (CRet a2 b2 p2)). intuition. inv H.
  eapply IHdstk; eauto.
Qed.

Lemma c_pop_to_return_spec3: forall s1 s2 b1 b2 p1 p2 a1 a2 dstk,
 c_pop_to_return (dstk ++ CRet a1 b1 p1 :: s2)
                    (CRet a2 b2 p2 :: s1) ->
 (forall e : CStkElmt, In e dstk -> exists a : @Atom T, e = CData a) ->
 s1 = s2 .
Proof.
  induction dstk; intros.
  inv H. auto.
  simpl in *. 
  inv H. destruct (H0 (CRet a2 b2 p2)). intuition. inv H.
  eapply IHdstk; eauto.
Qed.

Inductive cstep : @CS T -> @CS T -> Prop := 
| cstep_nop : forall m i s pcv pcl rl rpcl p m' pcv' pcl' p' i' s',
    index_list_Z pcv i = Some Noop ->
    check_addr_priv p pcv privInstSize ->
    run_tmu cstep OpNoop None None None pcl (CState m i s (pcv,pcl) p) (CState m' i' s' (pcv',pcl') p')  ->    
    cache_hit_read m' p' rl rpcl -> 
    cstep (CState m i s (pcv,pcl) p) (CState m' i' s' (pcv+1,rpcl) p')

| cstep_add: forall m i s rpcl pcv  pcl p rl x1v x1v' x1l x1l' x2v  x2v' x2l x2l' pcv' pcl' m' p' i' s', 
    index_list_Z pcv i = Some Add ->
    check_addr_priv p pcv privInstSize ->
    run_tmu cstep OpAdd (Some x1l) (Some x2l) None pcl 
            (CState m i (CData (x1v,x1l)::(CData (x2v,x2l))::s) (pcv,pcl) p) 
            (CState m' i' (CData (x1v',x1l')::(CData (x2v',x2l'))::s') (pcv',pcl') p') ->
    cache_hit_read m' p' rl rpcl -> 
    cstep (CState m i (CData (x1v,x1l)::(CData (x2v,x2l))::s) (pcv,pcl) p) 
          (CState m' i ((CData (x1v'+x2v',rl))::s') (pcv'+1,rpcl) p')

| cstep_sub: forall m i s pcv pcl rpcl p rl x1v x1v' x1l m' x1l' x2v  x2v' x2l x2l' pcv' pcl' p' i' s', 
    index_list_Z pcv i = Some Sub ->
    check_addr_priv p pcv privInstSize ->
    run_tmu cstep OpSub (Some x1l) (Some x2l) None pcl 
            (CState m i (CData (x1v,x1l)::(CData (x2v,x2l))::s) (pcv,pcl) p)
            (CState m' i (CData (x1v',x1l')::(CData (x2v',x2l'))::s) (pcv',pcl') p') ->    
    cache_hit_read m' p' rl rpcl -> 
    cstep (CState m i (CData (x1v,x1l)::(CData (x2v,x2l))::s) (pcv,pcl) p) 
          (CState m' i' ((CData (x1v'-x2v',rl))::s') (pcv'+1,rpcl) p')

| cstep_push: forall m i s cv cl pcv pcl rpcl p rl m' i' s' p' pcv' pcl', 
    index_list_Z pcv i = Some (Push (cv,cl)) ->
    check_addr_priv p pcv privInstSize ->
    run_tmu cstep OpPush (Some cl) None None pcl (CState m i s (pcv,pcl) p) (CState m' i' s' (pcv',pcl') p') ->  
    cache_hit_read m' p' rl rpcl ->     
    cstep (CState m i s (pcv,pcl) p) 
          (CState m' i' ((CData (cv,rl))::s') (pcv'+1,rpcl) p')

| cstep_load: forall m i s pcv pcl addrv addrl xv xl rl rpcl p m' p' s' i' addrv' addrl' xv' xl' pcl' pcv', 
    index_list_Z pcv i = Some Load ->
    check_addr_priv p pcv privInstSize ->
    index_list_Z addrv m = Some (xv,xl) ->
    run_tmu cstep OpLoad (Some addrl) (Some xl) None pcl 
            (CState m i ((CData (addrv,addrl))::s) (pcv,pcl) p) 
            (CState m' i' ((CData (addrv',addrl'))::s) (pcv',pcl') p') ->    
    index_list_Z addrv' m' = Some (xv',xl') ->
    cache_hit_read m' p' rl rpcl ->     
    cstep (CState m i ((CData (addrv,addrl))::s) (pcv,pcl) p) 
          (CState m' i' ((CData (xv, rl))::s') (pcv'+1,rpcl) p')

| cstep_store: forall m i i' s pcv pcv' pcl pcl' addrv addrl addrv' addrl' xv xl xv' xl' mv ml mv' ml' rpcl rl p m' m'' s' p', 
    index_list_Z pcv i = Some Store ->
    check_addr_priv p pcv privInstSize ->
    index_list_Z addrv m = Some (mv,ml) ->
    run_tmu cstep OpStore (Some addrl) (Some xl) (Some ml) pcl 
            (CState m i ((CData (addrv,addrl))::(CData (xv,xl))::s) (pcv,pcl) p) 
            (CState m' i' ((CData (addrv',addrl'))::(CData (xv',xl'))::s') (pcv',pcl') p') ->    
    cache_hit_read m' p' rl rpcl ->     
    index_list_Z addrv' m' = Some (mv',ml') ->
    update_list_Z addrv' (xv', rl) m' = Some m'' ->
    cstep (CState m i ((CData (addrv,addrl))::(CData (xv,xl))::s) (pcv,pcl) p)
          (CState m'' i' s' (pcv'+1,rpcl) p')

| cstep_jump: forall m i i' s pcv pcl pcv' pcl' pcj pcjl rl rpcl m' p p' s', 
              forall pcj' pcjl',
    index_list_Z pcv i = Some Jump ->
    check_addr_priv p pcv privInstSize ->
    run_tmu cstep OpJump (Some pcjl) None None pcl 
            (CState m i ((CData (pcj,pcjl))::s) (pcv,pcl) p) 
            (CState m' i' ((CData (pcj',pcjl'))::s') (pcv',pcl') p') ->    
    cache_hit_read m' p' rl rpcl ->     
    cstep (CState m i ((CData (pcj,pcjl))::s) (pcv,pcl) p) 
          (CState m' i' s' (pcj',rpcl) p')
               
| cstep_branchnz: forall m i i' s s' pcv pcl offv av al av' al' rl p rpcl p' m' pcv' pcl',
    index_list_Z pcv i = Some (BranchNZ offv) -> (* relative target *)
    check_addr_priv p pcv privInstSize ->
    run_tmu cstep  OpBranchNZ (Some al) None None pcl
            (CState m i ((CData (av,al))::s) (pcv,pcl) p)
            (CState m' i' ((CData (av',al'))::s') (pcv',pcl') p') ->    
    cache_hit_read m' p' rl rpcl ->     
    cstep (CState m i ((CData (av,al))::s) (pcv,pcl) p) 
          (CState m' i' s' (if av' =? 0 then pcv'+1 else pcv'+offv, rpcl) p')

| cstep_call: forall m i s pcv pcl pcv' pcl' rl rpcl args a r p' i' pcc pccl m' p s', 
              forall pcc' pccl' rpcl' args',
    index_list_Z pcv i = Some (Call a r) -> 
    check_addr_priv p pcv privInstSize ->
    length args = a -> (forall a, In a args -> exists d, a = CData d) ->
    length args' = a -> (forall a, In a args' -> exists d, a = CData d) ->
    run_tmu cstep  OpCall (Some pcl') None None pcl
            (CState m i ((CData (pcc,pccl))::args++s) (pcv,pcl) p) 
            (CState m' i' ((CData (pcc',pccl'))::args'++s') (pcv',pcl') p')  ->    
    cache_hit_read m' p' rl rpcl ->     
    cstep (CState m i ((CData (pcc,pccl))::args++s) (pcv,pcl) p) 
          (CState m' i' (args'++(CRet (pcv'+1,(if p' then pcl' else rl)) r p')::s') 
                  (pcc', if p' then pccl' else rpcl') p')

| cstep_ret: forall m i s pcv pcl pcv' pcl' rl rpcl p' i' m' p s' pcret pcretl s'' pret, 
    index_list_Z pcv i = Some Ret -> 
    check_addr_priv p pcv privInstSize ->
    run_tmu cstep OpRet (Some pcl') None None pcl
            (CState m i s (pcv,pcl) p)
            (CState m' i' s' (pcv',pcl') p') ->    
    c_pop_to_return s' ((CRet (pcret,pcretl) false pret)::s'') ->
    cache_hit_read m' p' rl rpcl ->     
    cstep (CState m i s (pcv,pcl) p) 
          (CState m' i' s'' (pcret, if p' then pcretl else rpcl) pret)

| cstep_vret: forall m i s pcv pcl pcv' pcl' rl rpcl p' i' m' p s' pcret pcretl s'' pret resv resl resv' resl', 
    index_list_Z pcv i = Some VRet -> 
    check_addr_priv p pcv privInstSize ->
    run_tmu cstep OpVRet (Some resl) (Some pcl') None pcl 
            (CState m i (CData (resv,resl)::s) (pcv,pcl) p)
            (CState m' i' (CData (resv',resl')::s') (pcv',pcl') p') ->
    c_pop_to_return s' ((CRet (pcret,pcretl) true pret)::s'') ->
    cache_hit_read m' p' rl rpcl ->     
    cstep (CState m i (CData (resv,resl)::s) (pcv,pcl) p) 
          (CState m' i' ((CData (resv',rl))::s'') (pcret, if p' then pcretl else rpcl) pret)
.

(* Success is reaching a Halt state in non-privileged mode and address. *)
Definition c_success (cs : @CS T) : Prop :=
  match index_list_Z (fst (pc cs)) (imem cs) with
  | Some Halt => is_true (negb (priv cs) && (fst (pc cs) >=? privInstSize))
  | _ => False
  end.

End CMach.

Hint Constructors check_tags run_tmu.


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
