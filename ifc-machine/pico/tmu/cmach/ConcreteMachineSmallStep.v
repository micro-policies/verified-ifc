Require Import List.
Require Import Omega.

Require Import Utils.
Require Import Lattices.
Require Import TMUInstr.
Require Import CLattices.
Require Import Concrete.

Set Implicit Arguments.
Local Open Scope Z_scope.

(** Reflexive transitive closure. *)
(* to be moved in Utils *)
Inductive star (S: Type) (Rstep: S -> S -> Prop): S -> S -> Prop :=
  | star_refl: forall s,
      star Rstep s s
  | star_step: forall s1 s2 s3,
      Rstep s1 s2 -> star Rstep s2 s3 -> 
      star Rstep s1 s3.

Section CMach.

Context {T: Type}
        {Latt : JoinSemiLattice T}
        {CLatt: ConcreteLattice T}.

Notation "i @ pc # instr" := (index_list_Z pc i = Some instr) (no associativity, at level 55).
Notation "'__'" := bot.
Notation fh_start := (0,__).
Notation fh_ret := (fun pc pcl => (CRet (pc,pcl) false false)).

(** Concrete machine transition relation.
    Each instructions has 3 semantic rules: (user mode - succ) (user mode - faulting) (kernel mode) *)

Inductive cstep : @CS T -> @CS T -> Prop := 
| cstep_nop : forall c m fh i s pcv pcl rl rpcl,
    forall (INST: i @ pcv # Noop)
           (CHIT: cache_hit c OpNoop (__,__,__) pcl)
           (CREAD: cache_hit_read c rl rpcl),
    cstep (CState c m fh i s (pcv,pcl) false)
          (CState c m fh i s (pcv+1,rpcl) false)

| cstep_nop_f : forall c c' m fh i s pcv pcl,
   forall (INST: i @ pcv # Noop)
          (CMISS: ~ cache_hit c OpNoop (__,__,__) pcl)
          (CUPD: c' = build_cache OpNoop (__,__,__)  pcl),
    cstep (CState c m fh i s (pcv,pcl) false) 
          (CState c' m fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_nop_p : forall c m fh i s pcv pcl,
    fh @ pcv # Noop ->
    cstep (CState c m fh i s (pcv,pcl) true) (CState c m fh i s (pcv+1,pcl) true)

| cstep_add: forall c fh m i s rpcl pcv pcl rl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Add)
         (CHIT: cache_hit c OpAdd (x1l, x2l, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           (CState c m fh i          ((x1v+x2v,rl):::s) (pcv+1,rpcl) false)

| cstep_add_f: forall c c' fh m i s pcv pcl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Add)
         (CMISS: ~ cache_hit c OpAdd (x1l, x2l, __) pcl)
         (CUPD: c' = build_cache OpAdd (x1l,x2l,__)  pcl),
     cstep (CState c  m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           (CState c' m fh i ((fh_ret pcv pcl)::(x1v,x1l):::(x2v,x2l):::s) fh_start true)

| cstep_add_p: forall c m fh i s pcv pcl x1v x1l x2v x2l, 
    fh @ pcv # Add ->
    cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true)  
          (CState c m fh i ((x1v+x2v,handlerLabel):::s) (pcv+1,pcl) true)

| cstep_sub: forall c fh m i s rpcl pcv  pcl rl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Sub)
         (CHIT: cache_hit c OpSub (x1l, x2l, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           (CState c m fh i          ((x1v-x2v,rl):::s) (pcv+1,rpcl) false)

| cstep_sub_f: forall c c' fh m i s pcv pcl x1v x1l x2v x2l,
   forall(INST: i @ pcv # Sub)
         (CMISS: ~ cache_hit c OpSub (x1l, x2l, __) pcl)
         (CUPD: c' = build_cache OpSub (x1l,x2l,__)  pcl),
     cstep (CState c  m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl)    false)  
           (CState c' m fh i ((fh_ret pcv pcl)::(x1v,x1l):::(x2v,x2l):::s) fh_start true)

| cstep_sub_p: forall c m fh i s pcv pcl x1v x1l x2v x2l, 
    fh @ pcv # Sub ->
    cstep (CState c m fh i ((x1v,x1l):::(x2v,x2l):::s) (pcv,pcl) true) 
          (CState c m fh i ((x1v-x2v,handlerLabel):::s) (pcv+1,pcl) true)

| cstep_push: forall c fh m i s rpcl pcv pcl rl cv cl,
   forall(INST: i @ pcv # Push (cv,cl))
         (CHIT: cache_hit c OpPush (cl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i s (pcv,pcl)   false)
           (CState c m fh i ((cv,rl):::s) (pcv+1,rpcl) false)

| cstep_push_f: forall c c' fh m i s pcv pcl cv cl,
   forall(INST : i @ pcv # Push (cv,cl))
         (CMISS: ~ cache_hit c OpPush (cl,__,__) pcl)
         (CUPD : c' = build_cache OpPush (cl,__,__) pcl),
     cstep (CState c  m fh i s (pcv,pcl) false)  
           (CState c' m fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_push_p: forall c m fh i s pcv pcl cv cl, 
    fh @ pcv # Push (cv,cl) ->
    cstep (CState c m fh i s (pcv,pcl) true) 
          (CState c m fh i ((cv,cl):::s) (pcv+1,pcl) true)

| cstep_load: forall c fh m i s rpcl pcv pcl rl addrv addrl xv xl,
   forall(INST: i @ pcv # Load)
         (CHIT: cache_hit c OpLoad (addrl, xl, __) pcl)
         (CREAD: cache_hit_read c rl rpcl)
         (MREAD: read_m addrv m = Some (xv,xl)),
     cstep (CState c m fh i ((addrv,addrl):::s) (pcv,pcl)   false)
           (CState c m fh i ((xv,rl):::s) (pcv+1,rpcl) false)

| cstep_load_f: forall c c' fh m i s pcv pcl addrv addrl xv xl,
   forall(INST: i @ pcv # Load)
         (CMISS: ~ cache_hit c OpLoad (addrl,xl,__) pcl)
         (MREAD: read_m addrv m = Some (xv,xl))
         (CUPD : c' = build_cache OpLoad (addrl,xl,__) pcl),
     cstep (CState c  m fh i ((addrv,addrl):::s) (pcv,pcl)   false)
           (CState c' m fh i ((fh_ret pcv pcl)::(addrv,addrl):::s) fh_start true)

| cstep_load_p: forall c m fh i s pcv pcl addrv addrl xv xl,
    fh @ pcv # Load ->
    read_m addrv c = Some (xv,xl) ->
    cstep (CState c m fh i ((addrv,addrl):::s) (pcv,pcl) true) 
          (CState c m fh i ((xv,handlerLabel):::s) (pcv+1,pcl) true)

| cstep_store: forall c fh m i s rpcl pcv pcl rl addrv addrl xv xl mv ml,
   forall(INST: i @ pcv # Store)
         (CHIT: cache_hit c OpStore (addrl, xl, ml) pcl)
         (CREAD: cache_hit_read c rl rpcl)
         (MREAD: read_m addrv m = Some (mv,ml)),
     cstep (CState c m fh i ((addrv,addrl):::(xv,xl):::s) (pcv,pcl)   false)
           (CState c m fh i s (pcv+1,rpcl) false)

| cstep_store_f: forall c c' fh m i s pcv pcl addrv addrl xv xl mv ml,
   forall(INST: i @ pcv # Store)
         (CMISS: ~ cache_hit c OpStore (addrl,xl,ml) pcl)
         (MREAD: read_m addrv m = Some (mv,ml))
         (CUPD : c' = build_cache OpStore (addrl,xl,ml) pcl),
     cstep (CState c  m fh i ((addrv,addrl):::(xv,xl):::s) (pcv,pcl)   false)
           (CState c' m fh i ((fh_ret pcv pcl)::(addrv,addrl):::(xv,xl):::s) fh_start true)

| cstep_store_p: forall c m fh i s pcv pcl c' addrv addrl x, 
    fh @ pcv # Store ->
    upd_m addrv x c = Some c' ->
    cstep (CState c m fh i ((addrv,addrl)::: x :::s) (pcv,pcl) true)
          (CState c' m fh i s (pcv+1,pcl) true)

| cstep_jump: forall c fh m i s rpcl pcv pcl rl cv cl,
   forall(INST: i @ pcv # Jump)
         (CHIT: cache_hit c OpJump (cl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((cv,cl):::s) (pcv,pcl)   false)
           (CState c m fh i s (cv,rpcl) false)

| cstep_jump_f: forall c c' fh m i s pcv pcl cv cl,
   forall(INST: i @ pcv # Jump)
         (CMISS: ~ cache_hit c OpJump (cl,__,__) pcl)
         (CUPD : c' = build_cache OpJump (cl,__,__) pcl),
     cstep (CState c  m fh i ((cv,cl):::s) (pcv,pcl)   false)
           (CState c' m fh i ((fh_ret pcv pcl)::(cv,cl):::s) fh_start true)

| cstep_jump_p: forall c m fh i s pcv pcl pcj pcjl,
    fh @ pcv # Jump ->
    cstep (CState c m fh i ((pcj,pcjl):::s) (pcv,pcl) true) 
          (CState c m fh i s (pcj,pcjl) true)

| cstep_bnz: forall c fh m i s rpcl pcv pcl rl cv cl offv,
   forall(INST: i @ pcv # BranchNZ offv)
         (CHIT: cache_hit c OpBranchNZ (cl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((cv,cl):::s) (pcv,pcl)   false)
           (CState c m fh i s (if cv =? 0 then pcv+1 else pcv+offv, rpcl) false)

| cstep_bnz_f: forall c c' fh m i s pcv pcl cv cl offv,
   forall(INST: i @ pcv # BranchNZ offv)
         (CMISS: ~ cache_hit c OpBranchNZ (cl,__,__) pcl)
         (CUPD : c' = build_cache OpBranchNZ (cl,__,__) pcl),
     cstep (CState c  m fh i ((cv,cl):::s) (pcv,pcl)   false)
           (CState c' m fh i ((fh_ret pcv pcl)::(cv,cl):::s) fh_start true)

| cstep_branchnz_p: forall c m fh i s pcv pcl offv av al,
    fh @ pcv # BranchNZ offv -> 
    cstep (CState c m fh i ((av,al):::s) (pcv,pcl) true) 
          (CState c m fh i s (if av =? 0 then pcv+1 else pcv+offv, handlerLabel) true)

| cstep_call: forall c fh m i s rpcl pcv pcl rl pcc pccl a r args,
   forall(INST: i @ pcv # Call a r)
         (ARGS: length args = a -> (forall a, In a args -> exists d, a = CData d))
         (CHIT: cache_hit c OpCall (pccl, __, __) pcl)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((pcc,pccl):::args++s) (pcv,pcl)   false)
           (CState c m fh i (args++(((CRet (pcv+1, rl)) r false)::s)) (pcc,rpcl) false)

| cstep_call_f: forall c c' fh m i s pcv pcl pcc pccl a r args,
   forall(INST: i @ pcv # Call a r)
         (ARGS: length args = a -> (forall a, In a args -> exists d, a = CData d))
         (CMISS: ~ cache_hit c OpCall (pccl, __, __) pcl)
         (CUPD : c' = build_cache OpCall (pccl,__,__) pcl),
     cstep (CState c  m fh i ((pcc,pccl):::args++s) (pcv,pcl)   false)
           (CState c' m fh i ((fh_ret pcv pcl)::(pcc,pccl):::args++s) fh_start true)

| cstep_call_p: forall c m fh i s pcv pcl a r args pcc pccl,
    fh @ pcv # Call a r -> 
    length args = a -> (forall a, In a args -> exists d, a = CData d) ->
    cstep (CState c m fh i ((pcc,pccl):::args++s) (pcv,pcl) true) 
          (CState c m fh i (args++(CRet (pcv+1, pcl) r true)::s) (pcc, pccl) true)

| cstep_ret: forall c fh m i s s' pcv pcl rl rpcl pcret pcretl,
   forall(INST: i @ pcv # Ret)
         (CHIT: cache_hit c OpRet (pcretl, __, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) false false)::s')) (*DD: should only return to user mode *)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i s  (pcv,pcl) false)
           (CState c m fh i s' (pcret, rpcl) false)

| cstep_ret_f: forall c c' fh m i s' s pcv pcl pcret pcretl,
   forall(INST: i @ pcv # Ret)
         (CMISS: ~ cache_hit c OpRet (pcretl, __, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) false false)::s')) (*DD: same thing *)
         (CUPD : c' = build_cache OpRet (pcretl,__,__) pcl),
     cstep (CState c m fh i s  (pcv,pcl) false)
           (CState c' m fh i ((fh_ret pcv pcl)::s) fh_start true)

| cstep_retv: forall c fh m i s s' pcv pcl rl rpcl resv resl pcret pcretl,
   forall(INST: i @ pcv # VRet)
         (CHIT: cache_hit c OpVRet (resl, pcretl, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) true false)::s')) (*DD: should only return to user mode *)
         (CREAD: cache_hit_read c rl rpcl),
     cstep (CState c m fh i ((resv,resl):::s)  (pcv,pcl) false)
           (CState c m fh i ((resv,rl):::s') (pcret,rpcl) false)

| cstep_ret_p: forall c m fh i s pcv pcl  pcret pcretl s' pret, 
    fh @ pcv # Ret -> (* can either return to user/priv mode *)
    c_pop_to_return s ((CRet (pcret,pcretl) false pret)::s') ->
    cstep (CState c m fh i s  (pcv,pcl) true) 
          (CState c m fh i s' (pcret,pcretl) pret)

| cstep_retv_f: forall c c' fh m i s' s pcv pcl resv resl pcret pcretl,
   forall(INST: i @ pcv # VRet)
         (CMISS: ~ cache_hit c OpVRet (resl, pcretl, __) pcl)
         (POP:  c_pop_to_return s ((CRet (pcret,pcretl) false false)::s')) (*DD: same thing *)
         (CUPD : c' = build_cache OpVRet (resl,pcretl,__) pcl),
     cstep (CState c m fh i ((resv,resl):::s)  (pcv,pcl) false)
           (CState c' m fh i ((fh_ret pcv pcl)::(resv,resl):::s) fh_start true)

| cstep_vret_p: forall c m fh i s pcv pcl s' pcret pcretl resv resl, 
    fh @ pcv # VRet -> (* cannot vreturn to user mode *)
    c_pop_to_return s ((CRet (pcret,pcretl) true true)::s') ->
    cstep (CState c m fh i ((resv,resl):::s) (pcv,pcl) true) 
          (CState c m fh i ((resv,resl):::s') (pcret, pcretl) true).

(* Success is reaching a Halt state in non-privileged mode and valid address. *)
Definition c_success (cs : @CS T) : Prop :=
  match index_list_Z (fst (pc cs)) (imem cs) with
  | Some Halt => is_true (negb (priv cs))
  | _ => False
  end.

End CMach.
