Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.
Require Import CLattices.
Require Import Concrete.

Set Implicit Arguments.
Local Open Scope Z_scope.

(* Require Import Coq.Unicode.Utf8.  *)

Section CMach.

Context {T: Type}
        {CLatt: ConcreteLattice T}.

Notation "i @ pc # instr" := (index_list_Z pc i = Some instr) (no associativity, at level 55).
Notation "'__'" := None.

(* Didn't get it to work for some reason *)
(* Notation "'≪' c , m , fh , i , s , pc '≫'" := (@CState T c m fh i s pc true) (at level 55, no associativity). *)
(* Notation "'〈' c, m , fh, i , s , pc '〉'" := (@CState T c m fh i s pc false) (at level 95, no associativity).*)
(* Definition state c m fh i s pc1 pc2 p := ≪ c , m , fh , i , s , (pc1,pc2) , p ≫. *)
 
(** The concrete machine in privileged mode. *)
Inductive cstep_p :  @CS T -> @CS T -> Prop := 
| cp_nop : forall c m fh i s pcv pcl,
    fh @ pcv # Noop ->
    cstep_p (CState c m fh i s (pcv,pcl) true) (CState c m fh i s (pcv+1,pcl) true)

| cp_add: forall c m fh i s pcv pcl x1v x1l x2v x2l, 
    fh @ pcv # Add ->
    cstep_p (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true)  
            (CState c m fh i ((x1v+x2v,handlerLabel):::s) (pcv+1,pcl) true)

| cp_sub: forall c m fh i s pcv pcl x1v x1l x2v x2l, 
    fh @ pcv # Sub ->
    cstep_p (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true) 
            (CState c m fh i ((x1v-x2v,handlerLabel):::s) (pcv+1,pcl) true)

| cp_push: forall c m fh i s pcv pcl cv cl, 
    fh @ pcv # Push (cv,cl) ->
    cstep_p (CState c m fh i s (pcv,pcl) true) 
            (CState c m fh i ((cv,cl):::s) (pcv+1,pcl) true)

| cp_load: forall c m fh i s pcv pcl addrv addrl xv xl,
    fh @ pcv # Load ->
    read_m addrv c = Some (xv,xl) ->
    cstep_p (CState c m fh i ((addrv,addrl):::s) (pcv,pcl) true) 
            (CState c m fh i ((xv,handlerLabel):::s) (pcv+1,pcl) true)

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
            (CState c m fh i s (if av =? 0 then pcv+1 else pcv+offv, handlerLabel) true)

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

| cp_vret: forall c m fh i s pcv pcl s' pcret pcretl pret resv resl, 
    fh @ pcv # VRet -> (* cannot vreturn to user mode *)
    c_pop_to_return s ((CRet (pcret,pcretl) true true)::s') ->
    cstep_p (CState c m fh i ((resv,resl):::s) (pcv,pcl) true) 
            (CState c m fh i ((resv,resl):::s') (pcret, pcretl) pret).


(** Cache handling mechanism *)
Definition mvector (opcode: OpCode) (op1lab op2lab op3lab:option T) (pclab: T) : Z * Z * Z * Z * Z :=
   let optlabToZ optl :=
     match optl with
     | None => labToZ bot
     | Some l => labToZ l 
     end in
   (opCodeToZ opcode, optlabToZ op1lab, optlabToZ op2lab, optlabToZ op3lab, labToZ pclab).

Definition rvector (tagr:Z) (tagrpc:Z) : T * T := (ZToLab tagr,ZToLab tagrpc). 

(* TMU.  If rule is in the cache (currently just a single entry),
   leave the state unchanged and return
   Some(result_tag,result_pc_tag); otherwise, set the state to invoke
   the TMU fault handler code and return None.  *)

(* [check_stags opc opl1 opl2 opl3 pcl s1 s2] holds when: either [s2]
has an up to date cache or [s2] is the privileged state in which the
tmu routine must then be executed *)
Inductive check_tags (opcode: OpCode) (opl1 opl2 opl3:option T) (pcl:T): @CS T -> @CS T -> Prop :=
| ct_upriv_chit : (* m vector is in the cache *)
    forall c m fh i s pc,
    forall (CHIT: cache_hit c (mvector opcode opl1 opl2 opl3 pcl)),      
      check_tags opcode opl1 opl2 opl3 pcl 
                 (CState c m fh i s pc false) (CState c m fh i s pc false)

| ct_upriv_cmiss: (* not in cache: arrange to enter TMU fault handler *)
    forall c c' m fh i s pc mvec,
      forall (MVEC: mvec = (mvector opcode opl1 opl2 opl3 pcl))
             (CMISS: ~ cache_hit c mvec)
             (C_UPD: cache_hit c' mvec),
    check_tags opcode opl1 opl2 opl3 pcl 
               (CState c m fh i s pc false) 
               (CState c' m fh i ((CRet pc false false)::s) (0,handlerLabel) true).

(* [run_tmu] checks the tags, and potentially execute all the code of
   the tmu fault handler and goes back to the unprivileged mode.  We
   check it does not fail by going ruling out pc (-1,handlerLabel) or
   demanding priv. bit of resulting state to be false.  If the fault
   handler fails, the concrete machine just does not step *) 
Inductive run_tmu (opcode: OpCode) (opl1 opl2 opl3:option T) (pcl:T) (cs: CS) : @CS T -> Prop :=
| rtmu_upriv : forall cs' c m s ppc fh i,
      priv cs = false ->
      pc cs = ppc ->
      check_tags opcode opl1 opl2 opl3 pcl cs cs' ->
      runsToEscape cstep_p 0 privInstSize cs' (CState c m fh i s ppc false) ->
      run_tmu opcode opl1 opl2 opl3 pcl cs (CState c m fh i s ppc false).


(** Concrete machine transition relation. Unprivileged mode. *)
Inductive cstep : @CS T -> @CS T -> Prop := 
| cstep_nop : forall c m fh i s pcv pcl rl rpcl p c' m' pcv' pcl' p' fh' i' s',
    i @ pcv # Noop ->
    run_tmu OpNoop __ __ __  pcl 
            (CState c m fh i s (pcv,pcl) p) 
            (CState c' m' fh' i' s' (pcv',pcl') p') ->
    cache_hit_read c' p' rl rpcl -> 
    cstep (CState c m fh i s (pcv,pcl) p) (CState c' m' fh' i' s' (pcv+1,rpcl) p')

| cstep_add: forall c c' fh fh' m i s rpcl pcv  pcl p rl x1v x1v' x1l x1l' x2v  x2v',
               forall x2l x2l' pcv' pcl' m' p' i' s', 
    i @ pcv # Add ->
    run_tmu OpAdd (Some x1l) (Some x2l) __ pcl 
            (CState c  m  fh  i  ((x1v,x1l):::(x2v,x2l):::s)      (pcv,pcl)   p) 
            (CState c' m' fh' i' ((x1v',x1l'):::(x2v',x2l'):::s') (pcv',pcl') p') ->
    cache_hit_read c' p' rl rpcl -> 
    cstep (CState c  m  fh  i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)     p )  
          (CState c' m' fh' i ((x1v'+x2v',rl):::s')       (pcv'+1,rpcl) p')

| cstep_sub: forall c c' fh fh' m i s pcv pcl rpcl p rl x1v x1v' x1l m' x1l' x2v,
             forall x2v' x2l x2l' pcv' pcl' p' i' s', 
    i @ pcv # Sub ->
    run_tmu OpSub (Some x1l) (Some x2l) __ pcl 
            (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) p)
            (CState c' m' fh' i ((x1v',x1l'):::(x2v',x2l'):::s) (pcv',pcl') p') ->    
    cache_hit_read c' p' rl rpcl -> 
    cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) p) 
          (CState c' m' fh' i' ((x1v'-x2v',rl):::s') (pcv'+1,rpcl) p')

| cstep_push: forall c fh c' fh' m i s cv cl pcv pcl rpcl p rl m' i' s' p' pcv' pcl', 
    i @ pcv # Push (cv,cl) ->
    run_tmu OpPush (Some cl) __ __ pcl 
            (CState c  m fh i s (pcv,pcl) p)
            (CState c' m' fh' i' s' (pcv',pcl') p') ->  
    cache_hit_read c' p' rl rpcl ->     
    cstep (CState c m fh i s (pcv,pcl) p) (CState c' m' fh' i' ((cv,rl):::s') (pcv'+1,rpcl) p')

| cstep_load: forall c c' fh fh' m i s pcv pcl addrv addrl xv xl rl rpcl p m' p' s' i',
              forall addrv' addrl' xv' xl' pcl' pcv', 
    i @ pcv # Load ->
    read_m addrv m = Some (xv,xl) ->
    run_tmu OpLoad (Some addrl) (Some xl) __ pcl 
            (CState c m fh i ((addrv,addrl):::s) (pcv,pcl) p) 
            (CState c' m' fh' i' ((addrv',addrl'):::s) (pcv',pcl') p') ->    
    read_m addrv' m' = Some (xv',xl') ->
    cache_hit_read c' p' rl rpcl ->     
    cstep (CState c m fh i ((addrv,addrl):::s) (pcv,pcl) p) 
          (CState c' m' fh' i' ((xv, rl):::s') (pcv'+1,rpcl) p')

| cstep_store: forall c c' fh fh' m i i' s pcv pcv' pcl pcl' addrv addrl addrv' addrl',
               forall xv xl xv' xl' mv ml mv' ml' rpcl rl p m' m'' s' p', 
    i @ pcv # Store ->
    read_m addrv m = Some (mv,ml) ->
    run_tmu OpStore (Some addrl) (Some xl) (Some ml) pcl 
            (CState c m fh i ((addrv,addrl):::(xv,xl):::s) (pcv,pcl) p) 
            (CState c' m' fh' i' ((addrv',addrl'):::(xv',xl'):::s') (pcv',pcl') p') ->    
    cache_hit_read c' p' rl rpcl ->     
    read_m addrv' m' = Some (mv',ml') ->
    upd_m addrv' (xv', rl) m' = Some m'' ->
    cstep (CState c m fh i ((addrv,addrl):::(xv,xl):::s) (pcv,pcl) p) 
          (CState c' m'' fh' i' s' (pcv'+1,rpcl) p')

| cstep_jump: forall c c' fh fh' m i i' s pcv pcl pcv' pcl' pcj pcjl rl rpcl m' p p' s' pcj' pcjl',
    i @ pcv # Jump ->
    run_tmu OpJump (Some pcjl) __ __ pcl 
            (CState c m fh i ((pcj,pcjl):::s) (pcv,pcl) p) 
            (CState c' m' fh' i' ((pcj',pcjl'):::s') (pcv',pcl') p') ->    
    cache_hit_read c' p' rl rpcl ->     
    cstep (CState c m fh i ((pcj,pcjl):::s) (pcv,pcl) p) 
          (CState c' m' fh' i' s' (pcj',rpcl) p')
               
| cstep_branchnz: forall c c' fh fh' m i i' s s' pcv pcl offv av al av' al' rl p rpcl p' m' pcv' pcl',
    i @ pcv # BranchNZ offv -> (* relative target *)
    run_tmu OpBranchNZ (Some al) __ __ pcl
            (CState c m fh i ((av,al):::s) (pcv,pcl) p)
            (CState c' m' fh' i' ((av',al'):::s') (pcv',pcl') p') ->    
    cache_hit_read c' p' rl rpcl ->     
    cstep (CState c m fh i ((av,al):::s) (pcv,pcl) p) 
          (CState c' m' fh' i' s' (if av' =? 0 then pcv'+1 else pcv'+offv, rpcl) p')

| cstep_call: forall c c' fh fh' m i s pcv pcl pcv' pcl' rl rpcl args a r p' i',
              forall pcc pccl m' p s' pcc' pccl' rpcl' args',
    i @ pcv # Call a r -> 
    length args = a -> (forall a, In a args -> exists d, a = CData d) ->
    length args' = a -> (forall a, In a args' -> exists d, a = CData d) ->
    run_tmu OpCall (Some pcl') __ __ pcl
            (CState c m fh i ((pcc,pccl):::args++s) (pcv,pcl) p) 
            (CState c' m' fh' i' ((pcc',pccl'):::args'++s') (pcv',pcl') p')  ->    
    cache_hit_read c' p' rl rpcl ->     
    cstep (CState c m fh i ((pcc,pccl):::args++s) (pcv,pcl) p) 
          (CState c' m' fh' i' (args'++(CRet (pcv'+1,(if p' then pcl' else rl)) r p')::s') 
                  (pcc', if p' then pccl' else rpcl') p')

| cstep_ret: forall c c' fh fh' m i s pcv pcl pcv' pcl' rl rpcl p' i' m' p s' pcret pcretl s'' pret, 
    i @ pcv # Ret -> 
    run_tmu OpRet (Some pcl') __ __ pcl
            (CState c m fh i s (pcv,pcl) p)
            (CState c' m' fh' i' s' (pcv',pcl') p') ->    
    c_pop_to_return s' ((CRet (pcret,pcretl) false pret)::s'') ->
    cache_hit_read c' p' rl rpcl ->     
    cstep (CState c m fh i s (pcv,pcl) p) 
          (CState c' m' fh' i' s'' (pcret, if p' then pcretl else rpcl) pret)

| cstep_vret: forall c c' fh fh' m i s pcv pcl pcv' pcl' rl rpcl p' i' m' p s' pcret pcretl,
              forall s'' pret resv resl resv' resl', 
    i @ pcv # VRet -> 
    run_tmu OpVRet (Some resl) (Some pcl') __ pcl 
            (CState c m fh i ((resv,resl):::s) (pcv,pcl) p)
            (CState c' m' fh' i' ((resv',resl'):::s') (pcv',pcl') p') ->
    c_pop_to_return s' ((CRet (pcret,pcretl) true pret)::s'') ->
    cache_hit_read c' p' rl rpcl ->     
    cstep (CState c m fh i ((resv,resl):::s) (pcv,pcl) p) 
          (CState c' m' fh' i' ((resv',rl):::s'') (pcret, if p' then pcretl else rpcl) pret)
.

(* Success is reaching a Halt state in non-privileged mode and address. *)
Definition c_success (cs : @CS T) : Prop :=
  match index_list_Z (fst (pc cs)) (imem cs) with
  | Some Halt => is_true (negb (priv cs) && (fst (pc cs) >=? privInstSize))
  | _ => False
  end.

End CMach.

Hint Constructors check_tags run_tmu.


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
